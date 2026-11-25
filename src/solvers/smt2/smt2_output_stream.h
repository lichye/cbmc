// Author: lichye

/// \file
/// SMT2 in-memory output stream.

#ifndef CPROVER_SOLVERS_SMT2_SMT2_OUTPUT_STREAM_H
#define CPROVER_SOLVERS_SMT2_SMT2_OUTPUT_STREAM_H

#include <exception>
#include <new>
#include <sstream>

/// Retain an allocation exception that ostream reports only as badbit.
/// The solver can inspect it after assertion conversion and before writing a
/// problem file, even if the stream state has been cleared in the meantime.
class smt2_output_streamt : public std::ostream
{
public:
  smt2_output_streamt() : std::ostream(nullptr)
  {
    rdbuf(&buffer);
  }

  std::string str() const
  {
    return buffer.str();
  }

  void str(const std::string &value)
  {
    buffer.str(value);
  }

  void rethrow_allocation_failure() const
  {
    if(buffer.allocation_failure)
      std::rethrow_exception(buffer.allocation_failure);
  }

private:
  struct buffert final : std::stringbuf
  {
    buffert() : std::stringbuf(std::ios::out)
    {
    }

    std::exception_ptr allocation_failure;

  protected:
    int_type overflow(int_type c) override
    try
    {
      return std::stringbuf::overflow(c);
    }
    catch(const std::bad_alloc &)
    {
      allocation_failure = std::current_exception();
      throw;
    }

    std::streamsize xsputn(const char *s, std::streamsize count) override
    try
    {
      return std::stringbuf::xsputn(s, count);
    }
    catch(const std::bad_alloc &)
    {
      allocation_failure = std::current_exception();
      throw;
    }
  };

  buffert buffer;
};

#endif // CPROVER_SOLVERS_SMT2_SMT2_OUTPUT_STREAM_H
