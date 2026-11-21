/// \file
/// Ground extensional array ranges for bit-vector-only SMT array solvers.

#include "smt2_conv.h"

#include <util/arith_tools.h>
#include <util/exception_utils.h>

#include <algorithm>
#include <limits>

// A row is an array value. In array ranges the BTOR solvers admit only
// bit-vectors, so assign rows keys and equate key equality with extensional
// array equality. Ordinary SMT select/store then also implement whole-row
// copies, including at indices outside the declared hardware range.
std::string smt2_convt::row_sort_key(const array_typet &type) const
{
  std::string key;
  const typet *t = &type;
  while(t->id() == ID_array)
  {
    const auto &a = to_array_type(*t);
    const auto &index = a.index_type();
    if(index.id() != ID_unsignedbv && index.id() != ID_signedbv)
      throw unsupported_operation_exceptiont("nested array needs a bit-vector index");
    key += std::to_string(boolbv_width(index)) + "/";
    t = &a.element_type();
  }
  if(t->id() == ID_bool && use_array_of_bool)
    return key + "Bool";
  if(t->id() != ID_unsignedbv && t->id() != ID_signedbv && t->id() != ID_bool)
    throw unsupported_operation_exceptiont("nested array needs a bit-vector or Boolean leaf");
  return key + std::to_string(boolbv_width(*t));
}

smt2_convt::row_sortt &smt2_convt::register_row_sort(
  const array_typet &type, std::size_t prefix_bits)
{
  auto key = row_sort_key(type);
  auto it = row_sorts.find(key);
  if(it == row_sorts.end())
  {
    const typet *t = &type;
    std::size_t bits = 0;
    while(t->id() == ID_array)
    {
      const auto &a = to_array_type(*t);
      bits += boolbv_width(a.index_type());
      t = &a.element_type();
    }
    it = row_sorts.emplace(
      key, row_sortt{row_sorts.size(), bits, boolbv_width(*t), 0, 1, type, {}}).first;
  }
  auto &sort = it->second;
  // The sampled pass is only a SAT witness search. Four coordinates
  // suffice for many small memories; a miss retries unrestricted rows.
  const auto extent = numeric_cast<std::size_t>(type.size());
  if(extent)
  {
    const auto index_width = boolbv_width(type.index_type());
    const std::size_t max_samples = index_width < 2 ? 1u << index_width : 4;
    sort.samples = std::max(sort.samples, std::min(*extent, max_samples));
  }
  const auto needed = std::numeric_limits<std::size_t>::digits + prefix_bits;
  if(needed > sort.key_bits)
  {
    sort.key_bits = needed;
    if(type.element_type().id() == ID_array)
      register_row_sort(
        to_array_type(type.element_type()), prefix_bits + boolbv_width(type.index_type()));
  }
  return sort;
}

std::size_t smt2_convt::row_key_width(const row_sortt &s) const
{
  if(sample_rows)
  {
    const auto &child = s.type.element_type();
    auto bits = child.id() == ID_array
                  ? row_key_width(row_sorts.at(row_sort_key(to_array_type(child))))
                  : s.leaf_bits;
    if(bits > std::numeric_limits<std::size_t>::max() / s.samples)
      throw unsupported_operation_exceptiont("sample row too wide");
    return bits * s.samples;
  }
  if(s.index_bits < std::numeric_limits<std::size_t>::digits &&
     s.leaf_bits <= (s.key_bits >> s.index_bits))
    return s.leaf_bits << s.index_bits;
  return s.key_bits;
}

void smt2_convt::write_array_prelude(std::ostream &stream) const
{
  for(const auto &entry : row_sorts)
  {
    const auto &s = entry.second;
    // At most SIZE_MAX ground array terms, each reaching at most 2^prefix
    // rows. Conversely every unused key must also admit a distinct row in
    // the original sort. The smaller of these bounds satisfies both.
    auto width = row_key_width(s);
    stream << "(define-sort |&row sort " << s.number
           << "| () (_ BitVec " << width << "))\n";
  }
}

// This is an injection: all bits of the key are observable at the sampled
// addresses. Other indices get a fixed default. A resulting SAT model thus
// extends to full arrays, including their unobserved coordinates.
void smt2_convt::write_sample_row(
  std::ostream &s, const row_sortt &sort, std::size_t row) const
{
  const auto index_bits = boolbv_width(sort.type.index_type());
  const auto word_bits = row_key_width(sort) / sort.samples;
  const bool boolean = sort.type.element_type().id() == ID_bool && use_array_of_bool;
  const auto array_sort = "(Array (_ BitVec " + std::to_string(index_bits) + ") " +
    (boolean ? "Bool" : "(_ BitVec " + std::to_string(word_bits) + ")") + ")";
  s << "(assert (= |&row value " << row << "| (let ((t |&row key " << row << "|)) ";
  for(std::size_t i = 0; i < sort.samples; ++i)
    s << "(store ";
  s << "((as const " << array_sort << ") "
    << (boolean ? "false" : "(_ bv0 " + std::to_string(word_bits) + ")") << ')';
  for(std::size_t i = 0; i < sort.samples; ++i)
  {
    s << " (_ bv" << i << ' ' << index_bits << ") ";
    if(boolean)
      s << "(= #b1 ";
    s << "((_ extract " << (i + 1) * word_bits - 1 << ' ' << i * word_bits << ") t)";
    if(boolean)
      s << ')';
    s << ')';
  }
  s << ")))\n";
}

std::size_t smt2_convt::register_row(const exprt &expr)
{
  auto inserted = row_terms.emplace(expr, row_count);
  if(!inserted.second)
    return inserted.first->second;
  const auto n = row_count++;
  auto &sort = register_row_sort(to_array_type(expr.type()), 0);
  sort.rows.push_back(n);
  const auto *index = expr_try_dynamic_cast<index_exprt>(expr);
  if(index && index->array().type().id() == ID_array && use_array_theory(index->array()))
  {
    out << "(declare-fun |&row value " << n << "| () ";
    convert_type(expr.type());
    out << ")\n(define-fun |&row key " << n << "| () |&row sort "
        << sort.number << "| (select ";
    convert_expr(index->array());
    out << ' ';
    convert_expr(typecast_exprt{index->index(), to_array_type(index->array().type()).index_type()});
    out << "))\n";
  }
  else
  {
    out << "(declare-fun |&row key " << n << "| () |&row sort "
        << sort.number << "|)\n(define-fun |&row value " << n << "| () ";
    convert_type(expr.type());
    out << ' ';
    if(use_array_theory(expr))
      convert_expr(expr);
    else
    {
      unflatten(wheret::BEGIN, expr.type());
      convert_expr(expr);
      unflatten(wheret::END, expr.type());
    }
    out << ")\n";
  }
  return n;
}

void smt2_convt::convert_stored_element(const exprt &expr)
{
  if(use_element_queries() && expr.type().id() == ID_array)
    out << "|&row key " << row_terms.at(expr) << '|';
  else
    convert_expr(expr);
}

void smt2_convt::write_row_equalities()
{
  for(const auto &entry : row_sorts)
  {
    const auto &rows = entry.second.rows;
    if(sample_rows)
    {
      for(auto i : rows)
        write_sample_row(out, entry.second, i);
      continue;
    }
    const auto width = row_key_width(entry.second);
    for(std::size_t i = 0; i < rows.size(); ++i)
    {
      // Keys are private. Rename observed values by order of occurrence
      // to eliminate permutations of otherwise unused key bits.
      if(width >= std::numeric_limits<std::size_t>::digits ||
         i < (std::size_t{1} << width))
        out << "(assert (bvule |&row key " << rows[i] << "| (_ bv" << i << ' '
            << width << ")))\n";
      for(std::size_t j = 0; j < i; ++j)
        out << "(assert (= (= |&row key " << rows[i] << "| |&row key " << rows[j]
            << "|) (= |&row value " << rows[i] << "| |&row value " << rows[j] << "|)))\n";
    }
  }
}

void smt2_convt::write_model_cells(
  const std::string &name,
  const std::string &array,
  const array_typet &type,
  bool declarations)
{
  const auto size = model_array_size(type);
  const auto &element = type.element_type();
  for(std::size_t i = 0; i < size; ++i)
  {
    const auto cell = model_element_id(name, i);
    if(element.id() == ID_array)
    {
      std::string value;
      if(declarations)
      {
        auto &sort = register_row_sort(to_array_type(element), boolbv_width(type.index_type()));
        const auto n = row_count++;
        sort.rows.push_back(n);
        value = "|&row value " + std::to_string(n) + "|";
        out << "(declare-fun " << value << " () ";
        convert_type(element);
        out << ")\n(define-fun |&row key " << n << "| () |&row sort "
            << sort.number << "| (select " << array << ' ';
        convert_expr(from_integer(i, type.index_type()));
        out << "))\n";
      }
      write_model_cells(cell, value, to_array_type(element), declarations);
    }
    else if(declarations)
    {
      out << "(define-fun |" << cell << "| () ";
      if(element.id() == ID_bool && !use_array_of_bool)
        out << "(_ BitVec 1)";
      else
        convert_type(element);
      out << " (select " << array << ' ';
      convert_expr(from_integer(i, type.index_type()));
      out << "))\n";
    }
    else
      out << "(get-value (|" << cell << "|))\n";
  }
}
