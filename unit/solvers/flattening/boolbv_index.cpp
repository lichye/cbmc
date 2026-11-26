/*******************************************************************\

Module: Unit tests for boolbvt::convert_index

Author: Crisp

\*******************************************************************/

/// \file
/// Unit tests for the range condition of a read from a uniform array

#include <util/arith_tools.h>
#include <util/bitvector_types.h>
#include <util/cout_message.h>
#include <util/std_expr.h>

#include <solvers/flattening/boolbv.h>
#include <solvers/sat/satcheck.h>
#include <testing-utils/empty_namespace.h>
#include <testing-utils/use_catch.h>

namespace
{
const unsignedbv_typet element_type{8};

array_typet array_type(std::size_t size)
{
  return array_typet{element_type, from_integer(size, unsignedbv_typet{32})};
}

/// A uniform array of `size` elements, all equal to 5.
array_exprt uniform(std::size_t size)
{
  exprt::operandst elements(size, from_integer(5, element_type));
  return array_exprt{std::move(elements), array_type(size)};
}

/// Whether a read of `array` at the index `value` of type `index_type` can
/// differ from 5. The index is a symbol, so that boolbvt does not resolve the
/// read at a constant index.
decision_proceduret::resultt differs(
  const exprt &array,
  const typet &index_type,
  const mp_integer &value)
{
  console_message_handlert message_handler;
  message_handler.set_verbosity(0);
  satcheckt satcheck{message_handler};
  boolbvt boolbv{empty_namespace, satcheck, message_handler};

  const symbol_exprt index{"index", index_type};
  boolbv << equal_exprt{index, from_integer(value, index_type)};
  boolbv << notequal_exprt{
    index_exprt{array, index, element_type}, from_integer(5, element_type)};
  return boolbv();
}

const auto known = decision_proceduret::resultt::D_UNSATISFIABLE;
const auto unconstrained = decision_proceduret::resultt::D_SATISFIABLE;
} // namespace

SCENARIO(
  "boolbvt_index_uniform_array",
  "[core][solvers][flattening][boolbvt][index]")
{
  GIVEN("An array size that the unsigned index type can represent")
  {
    const unsignedbv_typet index_type{2};

    THEN("The last element has the value, the size is out of bounds")
    {
      REQUIRE(differs(uniform(3), index_type, 0) == known);
      REQUIRE(differs(uniform(3), index_type, 2) == known);
      REQUIRE(differs(uniform(3), index_type, 3) == unconstrained);
    }
  }

  GIVEN("An array size above the largest value of the unsigned index type")
  {
    THEN("Every index of the type reads the value")
    {
      REQUIRE(differs(uniform(2), unsignedbv_typet{1}, 0) == known);
      REQUIRE(differs(uniform(2), unsignedbv_typet{1}, 1) == known);
      REQUIRE(differs(uniform(4), unsignedbv_typet{2}, 3) == known);
      REQUIRE(differs(uniform(5), unsignedbv_typet{2}, 3) == known);
    }
  }

  GIVEN("A signed index type")
  {
    THEN("A representable size keeps the upper bound")
    {
      const signedbv_typet index_type{3};
      REQUIRE(differs(uniform(3), index_type, 2) == known);
      REQUIRE(differs(uniform(3), index_type, 3) == unconstrained);
      REQUIRE(differs(uniform(3), index_type, -1) == unconstrained);
    }

    THEN("A size above the largest value bounds the non-negative indices")
    {
      const signedbv_typet index_type{2};
      REQUIRE(differs(uniform(2), index_type, 0) == known);
      REQUIRE(differs(uniform(2), index_type, 1) == known);
      REQUIRE(differs(uniform(2), index_type, -1) == unconstrained);
      REQUIRE(differs(uniform(2), index_type, -2) == unconstrained);
    }
  }

  GIVEN("An array_of expression")
  {
    THEN("A size above the largest value of the index type is handled alike")
    {
      const array_of_exprt array{from_integer(5, element_type), array_type(2)};
      REQUIRE(differs(array, unsignedbv_typet{1}, 1) == known);
      const array_of_exprt array3{
        from_integer(5, element_type), array_type(3)};
      REQUIRE(differs(array3, unsignedbv_typet{2}, 2) == known);
      REQUIRE(differs(array3, unsignedbv_typet{2}, 3) == unconstrained);
    }
  }
}
