/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "smt2_dec.h"

#include <util/invariant.h>
#include <util/message.h>
#include <util/run.h>
#include <util/tempfile.h>

#include "smt2irep.h"

#include <fstream>

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

  temporary_filet temp_file_problem("smt2_dec_problem_", ""),
    temp_file_stdout("smt2_dec_stdout_", ""),
    temp_file_stderr("smt2_dec_stderr_", "");

  if(assumption.is_not_nil())
    assumptions.push_back(convert(assumption));
  if(use_element_queries())
  {
    cached_output << array_body.str();
    array_body.str({});
  }
  else
  {
    cached_output << stringstream.str();
    stringstream.str({});
  }

  const auto write_problem = [&](bool get_model, bool exact_rows) {
    write_footer(get_model, exact_rows);
    std::ofstream problem_out(temp_file_problem());
    if(use_element_queries())
    {
      write_header(problem_out);
      write_array_prelude(problem_out);
      problem_out << cached_output.str() << array_body.str();
      array_body.str({});
    }
    else
    {
      problem_out << cached_output.str() << stringstream.str();
      stringstream.str({});
    }
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

  auto solve = [&](bool get_model, bool exact_rows) {
    write_problem(get_model, exact_rows);
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
  sample_rows = false;
  if(assumption.is_not_nil())
    assumptions.pop_back();
  return result;
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
