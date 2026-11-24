/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "smt2_dec.h"

#include <util/exception_utils.h>
#include <util/invariant.h>
#include <util/message.h>
#include <util/run.h>
#include <util/tempfile.h>

#include "smt2irep.h"

#include <array>
#include <cerrno>
#include <fstream>
#include <new>
#include <optional>
#include <stdexcept>
#include <system_error>

namespace
{
struct smt2_stream_failuret
{
  std::ios::iostate state;
  int file_error;
};

void check_smt2_stream(const std::ios &stream, int file_error = 0)
{
  if(!stream.good())
    throw smt2_stream_failuret{stream.rdstate(), file_error};
}
} // namespace

std::string smt2_dect::decision_procedure_text() const
{
  // clang-format off
  return "SMT2 " + logic + (use_FPA_theory ? " (with FPA)" : "") + " using " +
    (solver==solvert::GENERIC?"Generic":
     solver==solvert::BITWUZLA?"Bitwuzla":
     solver==solvert::BOOLECTOR?"Boolector":
     solver==solvert::CPROVER_SMT2?"CPROVER SMT2":
     solver==solvert::CVC5?"CVC5":
     solver==solvert::MATHSAT?"MathSAT":
     solver==solvert::YICES?"Yices":
     solver==solvert::Z3?"Z3":
     "(unknown)");
  // clang-format on
}

decision_proceduret::resultt smt2_dect::dec_solve(const exprt &assumption)
{
  ++number_of_solver_calls;
  if(query_output_failed)
    return resultt::D_ERROR;

  messaget log{message_handler};
  const auto output_error = [&](const char *stage) -> messaget::mstreamt &
  {
    query_output_failed = true;
    return log.error() << "SMT2 query output failed while " << stage << ": ";
  };
  const auto checked_output = [&](const char *stage, const auto &operation)
  {
    try
    {
      operation();
      return true;
    }
    catch(const smt2_stream_failuret &failure)
    {
      auto &message = output_error(stage);
      message << "stream set";
      if(failure.state & std::ios::badbit)
        message << " badbit";
      if(failure.state & std::ios::failbit)
        message << " failbit";
      if(failure.state & std::ios::eofbit)
        message << " eofbit";
      if(failure.file_error)
        message << " (" << failure.file_error << ": "
                << std::error_code(failure.file_error, std::generic_category())
                     .message()
                << ')';
      message << messaget::eom;
    }
    catch(const std::bad_alloc &)
    {
      output_error(stage) << "out of memory" << messaget::eom;
    }
    catch(const std::length_error &error)
    {
      output_error(stage) << error.what() << messaget::eom;
    }
    catch(const std::ios::failure &error)
    {
      output_error(stage) << error.what() << messaget::eom;
    }
    catch(const system_exceptiont &error)
    {
      output_error(stage) << error.what() << messaget::eom;
    }
    catch(...)
    {
      query_output_failed = true;
      throw;
    }
    return false;
  };

  const auto generated_text = [&]
  { return use_element_queries() ? array_body.str() : stringstream.str(); };
  const auto clear_generated_text = [&]
  {
    if(use_element_queries())
      array_body.str({});
    else
      stringstream.str({});
  };
  bool added_assumption = false;
  const auto finish = [&](resultt result)
  {
    sample_rows = false;
    if(added_assumption)
      assumptions.pop_back();
    return result;
  };

  if(
    !checked_output(
      "generating the SMT2 body",
      [&]
      {
        check_smt2_stream(out);
        if(assumption.is_not_nil())
        {
          assumptions.push_back(convert(assumption));
          added_assumption = true;
        }
        check_smt2_stream(out);
      }) ||
    !checked_output(
      "caching the SMT2 body",
      [&]
      {
        check_smt2_stream(cached_output);
        // Preserve an allocation exception from the string buffer instead of
        // letting the insertion reduce it to a generic stream error.
        cached_output.exceptions(std::ios::badbit);
        cached_output << generated_text();
        check_smt2_stream(cached_output);
        clear_generated_text();
      }))
    return finish(resultt::D_ERROR);

  std::optional<std::array<temporary_filet, 3>> files;
  if(!checked_output(
       "creating the SMT2 solver temporary files",
       [&]
       {
         files.emplace(std::array<temporary_filet, 3>{
           temporary_filet{"smt2_dec_problem_", ""},
           temporary_filet{"smt2_dec_stdout_", ""},
           temporary_filet{"smt2_dec_stderr_", ""}});
       }))
    return finish(resultt::D_ERROR);
  const auto &[temp_file_problem, temp_file_stdout, temp_file_stderr] = *files;

  const auto write_problem = [&](bool get_model, bool exact_rows)
  {
    if(!checked_output(
         "generating the SMT2 footer",
         [&]
         {
           check_smt2_stream(out);
           write_footer(get_model, exact_rows);
           check_smt2_stream(out);
         }))
      return false;

    std::ofstream problem_out;
    const auto file_operation = [&](const auto &operation)
    {
      errno = 0;
      operation();
      check_smt2_stream(problem_out, errno);
    };
    const auto write_text = [&](const std::string &text)
    { file_operation([&] { problem_out << text; }); };
    if(!checked_output(
         "opening the SMT2 problem file",
         [&]
         {
           const auto filename = temp_file_problem();
           file_operation([&] { problem_out.open(filename); });
         }))
      return false;
    if(
      use_element_queries() &&
      !checked_output(
        "writing the SMT2 header and array prelude",
        [&]
        {
          file_operation([&] { write_header(problem_out); });
          file_operation([&] { write_array_prelude(problem_out); });
        }))
      return false;
    if(!checked_output(
         "writing the SMT2 body and footer",
         [&]
         {
           check_smt2_stream(cached_output);
           write_text(cached_output.str());
           write_text(generated_text());
           file_operation([&] { problem_out.flush(); });
         }))
      return false;
    if(!checked_output(
         "closing the SMT2 problem file",
         [&] { file_operation([&] { problem_out.close(); }); }))
      return false;
    return checked_output(
      "resetting the SMT2 footer buffer", clear_generated_text);
  };

  std::vector<std::string> argv;
  std::string stdin_filename;

  auto solver_binary_name = [this](const std::string &solver_name)
  {
    if(solver_binary_or_empty.empty())
      return solver_name;
    else
      return solver_binary_or_empty;
  };

  switch(solver)
  {
  case solvert::BITWUZLA:
    argv = {solver_binary_name("bitwuzla"), temp_file_problem()};
    break;

  case solvert::BOOLECTOR:
    argv = {solver_binary_name("boolector"), "--smt2", temp_file_problem()};
    break;

  case solvert::CPROVER_SMT2:
    argv = {solver_binary_name("smt2_solver")};
    stdin_filename = temp_file_problem();
    break;

  case solvert::CVC5:
    argv = {
      solver_binary_name("cvc5"), "--lang", "smtlib", temp_file_problem()};
    break;

  case solvert::MATHSAT:
    // The options below were recommended by Alberto Griggio
    // on 10 July 2013

    argv = {
      solver_binary_name("mathsat"),
      "-input=smt2",
      "-preprocessor.toplevel_propagation=true",
      "-preprocessor.simplification=7",
      "-dpll.branching_random_frequency=0.01",
      "-dpll.branching_random_invalidate_phase_cache=true",
      "-dpll.restart_strategy=3",
      "-dpll.glucose_var_activity=true",
      "-dpll.glucose_learnt_minimization=true",
      "-theory.bv.eager=true",
      "-theory.bv.bit_blast_mode=1",
      "-theory.bv.delay_propagated_eqs=true",
      "-theory.fp.mode=1",
      "-theory.fp.bit_blast_mode=2",
      "-theory.arr.mode=1"};

    stdin_filename = temp_file_problem();
    break;

  case solvert::YICES:
    //    command = "yices -smt -e "   // Calling convention for older versions
    // Convention for 2.2.1
    argv = {solver_binary_name("yices-smt2"), temp_file_problem()};
    break;

  case solvert::Z3:
    argv = {solver_binary_name("z3"), "-smt2", temp_file_problem()};
    break;

  case solvert::GENERIC:
    PRECONDITION(!solver_binary_or_empty.empty());
    argv = {solver_binary_or_empty, temp_file_problem()};
    break;
  }

  auto solve = [&](bool get_model, bool exact_rows)
  {
    if(!write_problem(get_model, exact_rows))
      return resultt::D_ERROR;
    const int status = run(
      argv[0], argv, stdin_filename, temp_file_stdout(), temp_file_stderr());
    std::ifstream in(temp_file_stdout());
    if(use_element_queries())
    {
      // BTOR frontends return 10/20. A solver can print a verdict and
      // subsequently fail (e.g. while printing a model).
      std::string verdict;
      std::getline(in, verdict);
      if(status == 20 && verdict == "unsat")
        return resultt::D_UNSATISFIABLE;
      if(status == 10 && verdict == "sat")
      {
        if(!get_model)
          return resultt::D_SATISFIABLE;
        in.clear();
        in.seekg(0);
        return read_result(in);
      }
      std::string diagnostic;
      std::getline(std::ifstream{temp_file_stderr()}, diagnostic);
      messaget{message_handler}.error()
        << argv[0] << " returned status " << status << " (" << verdict << ") "
        << diagnostic << messaget::eom;
      return resultt::D_ERROR;
    }
    if(status < 0)
    {
      messaget{message_handler}.error() << "error running SMT2 solver"
                                       << messaget::eom;
      return resultt::D_ERROR;
    }
    return read_result(in);
  };

  // Query values only on SAT. Some SMT-LIB frontends reject get-value
  // after UNSAT, and finite memories can have many model elements.
  auto result = solve(!use_element_queries(), false);
  // Omitting row consistency is a relaxation: UNSAT is final, SAT requires
  // the exact encoding. Avoid constructing pairwise constraints for a cone
  // whose property is already decided without any row observations.
  if(!row_terms.empty() && result == resultt::D_SATISFIABLE)
  {
    sample_rows = true;
    result = solve(false, true);
    if(result == resultt::D_UNSATISFIABLE)
    {
      sample_rows = false;
      result = solve(false, true);
    }
  }
  if(use_element_queries() && result == resultt::D_SATISFIABLE)
  {
    result = solve(true, true);
    if(result == resultt::D_UNSATISFIABLE)
    {
      messaget{message_handler}.error()
        << "SMT2 solver returned inconsistent results during model extraction"
        << messaget::eom;
      result = resultt::D_ERROR;
    }
  }
  return finish(result);
}

static std::string drop_quotes(std::string src)
{
  if(src.size() >= 2 && src.front() == '|' && src.back() == '|')
    return std::string(src, 1, src.size() - 2);
  else
    return src;
}

decision_proceduret::resultt smt2_dect::read_result(std::istream &in)
{
  std::string line;
  decision_proceduret::resultt res=resultt::D_ERROR;

  boolean_assignment.clear();
  boolean_assignment.resize(no_boolean_variables, false);

  typedef std::unordered_map<irep_idt, irept> valuest;
  valuest parsed_values;

  while(in)
  {
    auto parsed_opt = smt2irep(in, message_handler);

    if(!parsed_opt.has_value())
      break;

    const auto &parsed = parsed_opt.value();

    if(parsed.id()=="sat")
      res=resultt::D_SATISFIABLE;
    else if(parsed.id()=="unsat")
      res=resultt::D_UNSATISFIABLE;
    else if(parsed.id() == "unknown")
    {
      messaget log{message_handler};
      log.error() << "SMT2 solver returned \"unknown\"" << messaget::eom;
      return decision_proceduret::resultt::D_ERROR;
    }
    else if(
      parsed.id().empty() && parsed.get_sub().size() == 1 &&
      parsed.get_sub().front().get_sub().size() == 2)
    {
      const irept &s0=parsed.get_sub().front().get_sub()[0];
      const irept &s1=parsed.get_sub().front().get_sub()[1];

      // Examples:
      // ( (B0 true) )
      // ( (|__CPROVER_pipe_count#1| (_ bv0 32)) )
      // ( (|some_integer| 0) )
      // ( (|some_integer| (- 10)) )

      parsed_values[s0.id()] = s1;
    }
    else if(
      parsed.id().empty() && parsed.get_sub().size() == 2 &&
      parsed.get_sub().front().id() == "error")
    {
      // We ignore errors after UNSAT because get-value after check-sat
      // returns unsat will give an error.
      if(res != resultt::D_UNSATISFIABLE)
      {
        const auto &message = id2string(parsed.get_sub()[1].id());
        messaget log{message_handler};
        log.error() << "SMT2 solver returned error message:\n"
                    << "\t" << messaget::quote_begin << message
                    << messaget::quote_end << messaget::eom;
        return decision_proceduret::resultt::D_ERROR;
      }
    }
  }

  // If the result is not satisfiable don't bother updating the assignments and
  // values (since we didn't get any), just return.
  if(res != resultt::D_SATISFIABLE)
    return res;

  for(auto &assignment : identifier_map)
  {
    const auto id = convert_identifier(assignment.first);
    const auto &type = assignment.second.type;
    if(!use_element_queries())
    {
      assignment.second.value = parse_rec(parsed_values[drop_quotes(id)], type);
      continue;
    }
    auto read_value = [&](const std::string &name, const typet &expected) {
      auto it = parsed_values.find(name);
      if(it == parsed_values.end())
        return exprt{nil_exprt{}};
      return parse_rec(it->second, expected);
    };

    if(type.id() == ID_array)
    {
      const auto read_array = [&](const auto &self, const std::string &name,
                                  const array_typet &array_type) -> exprt {
        const auto size = model_array_size(array_type);
        const auto &element = array_type.element_type();
        exprt::operandst cells;
        cells.reserve(size);
        for(std::size_t i = 0; i < size; ++i)
        {
          const auto cell_id = model_element_id(name, i);
          auto cell = element.id() == ID_array
                        ? self(self, cell_id, to_array_type(element))
                        : read_value(cell_id, element);
          if(cell.is_nil())
          {
            messaget{message_handler}.error()
              << "missing SMT2 model element " << cell_id << messaget::eom;
            return nil_exprt{};
          }
          cells.push_back(std::move(cell));
        }
        return array_exprt{std::move(cells), array_type};
      };
      assignment.second.value = read_array(read_array, id, to_array_type(type));
      if(assignment.second.value.is_nil())
        return resultt::D_ERROR;
    }
    else
    {
      assignment.second.value = read_value(drop_quotes(id), type);
      if(smt2_identifiers.count(id) && assignment.second.value.is_nil())
      {
        messaget{message_handler}.error()
          << "missing or invalid SMT2 model value for " << id << messaget::eom;
        return resultt::D_ERROR;
      }
    }
  }

  // Booleans
  for(unsigned v=0; v<no_boolean_variables; v++)
  {
    const std::string boolean_identifier =
      convert_identifier("B" + std::to_string(v));
      const auto found_parsed_value =
        parsed_values.find(drop_quotes(boolean_identifier));
      if(found_parsed_value != parsed_values.end())
      {
        const irept &value = found_parsed_value->second;

        const auto decoded = parse_rec(value, bool_typet{});
        if(decoded.is_nil())
        {
          messaget log{message_handler};
          log.error() << "SMT2 solver returned non-constant value for variable "
                      << boolean_identifier << messaget::eom;
          return decision_proceduret::resultt::D_ERROR;
        }
        boolean_assignment[v] = decoded.is_true();
      }
      else
      {
        // Work out the value based on what set_to was called with.
        const auto found_set_value = set_values.find(boolean_identifier);
        if(found_set_value != set_values.end())
          boolean_assignment[v] = found_set_value->second;
        else
        {
          messaget{message_handler}.error()
            << "missing SMT2 model value for Boolean " << boolean_identifier
            << messaget::eom;
          return resultt::D_ERROR;
        }
      }
  }

  return res;
}
