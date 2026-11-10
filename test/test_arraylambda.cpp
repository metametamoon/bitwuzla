/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */

#include "test.h"

class TestArrayLambda : public TestBitwuzla
{
 protected:
  void SetUp() override
  {
    TestBitwuzla::SetUp();
    bitwuzla_set_option(d_bzla, BITWUZLA_OPT_INCREMENTAL, 1);
    bitwuzla_set_option(d_bzla, BITWUZLA_OPT_PRODUCE_MODELS, 1);
    d_bv8   = bitwuzla_mk_bv_sort(d_bzla, 8);
    d_bv64  = bitwuzla_mk_bv_sort(d_bzla, 64);
    d_array = bitwuzla_mk_array_sort(d_bzla, d_bv8, d_bv8);
  }

  const BitwuzlaTerm *byte(uint64_t value)
  {
    return bitwuzla_mk_bv_value_uint64(d_bzla, d_bv8, value);
  }

  const BitwuzlaTerm *byte_const(const char *symbol)
  {
    return bitwuzla_mk_const(d_bzla, d_bv8, symbol);
  }

  const BitwuzlaTerm *term(BitwuzlaKind kind,
                           const BitwuzlaTerm *a,
                           const BitwuzlaTerm *b)
  {
    return bitwuzla_mk_term2(d_bzla, kind, a, b);
  }

  const BitwuzlaTerm *term(BitwuzlaKind kind,
                           const BitwuzlaTerm *a,
                           const BitwuzlaTerm *b,
                           const BitwuzlaTerm *c)
  {
    return bitwuzla_mk_term3(d_bzla, kind, a, b, c);
  }

  const BitwuzlaTerm *written_constant_array()
  {
    return term(BITWUZLA_KIND_ARRAY_STORE,
                bitwuzla_mk_const_array(d_bzla, d_array, byte(0)),
                byte(1),
                byte(2));
  }

  const BitwuzlaTerm *copy_overriding_last_index(const BitwuzlaTerm *array)
  {
    const BitwuzlaTerm *k = bitwuzla_mk_var(d_bzla, d_bv8, "k");
    return term(BITWUZLA_KIND_LAMBDA,
                k,
                term(BITWUZLA_KIND_ITE,
                     term(BITWUZLA_KIND_EQUAL, k, byte(0xff)),
                     byte(0),
                     term(BITWUZLA_KIND_ARRAY_SELECT, array, k)));
  }

  void assert_nonzero_read_back_from_free_array(const BitwuzlaTerm *value)
  {
    const BitwuzlaTerm *out = term(BITWUZLA_KIND_ARRAY_STORE,
                                   term(BITWUZLA_KIND_ARRAY_STORE,
                                        bitwuzla_mk_const(d_bzla, d_array, "a"),
                                        byte(0),
                                        value),
                                   byte_const("j"),
                                   byte_const("w"));
    bitwuzla_assert(d_bzla,
                    term(BITWUZLA_KIND_DISTINCT,
                         term(BITWUZLA_KIND_ARRAY_SELECT, out, byte_const("r")),
                         byte(0)));
  }

  void assert_copy_read_at(const BitwuzlaTerm *index)
  {
    const BitwuzlaTerm *copy =
        copy_overriding_last_index(written_constant_array());
    assert_nonzero_read_back_from_free_array(
        term(BITWUZLA_KIND_APPLY, copy, index));
  }

  const BitwuzlaTerm *stores_over(const BitwuzlaTerm *array)
  {
    for (uint64_t offset = 0; offset < 8; ++offset)
    {
      array = term(BITWUZLA_KIND_ARRAY_STORE,
                   array,
                   bitwuzla_mk_bv_value_uint64(d_bzla, d_bv64, offset),
                   byte(offset + 1));
    }
    return array;
  }

  const BitwuzlaSort *d_bv8   = nullptr;
  const BitwuzlaSort *d_bv64  = nullptr;
  const BitwuzlaSort *d_array = nullptr;
};

TEST_F(TestArrayLambda, read_of_copy_outside_override)
{
  const BitwuzlaTerm *p = byte_const("p");
  bitwuzla_assert(d_bzla, term(BITWUZLA_KIND_DISTINCT, p, byte(0xff)));
  assert_copy_read_at(p);
  ASSERT_EQ(bitwuzla_check_sat(d_bzla), BITWUZLA_SAT);
}

TEST_F(TestArrayLambda, read_of_copy_at_override)
{
  const BitwuzlaTerm *p = byte_const("p");
  bitwuzla_assert(d_bzla, term(BITWUZLA_KIND_EQUAL, p, byte(0xff)));
  assert_copy_read_at(p);
  ASSERT_EQ(bitwuzla_check_sat(d_bzla), BITWUZLA_SAT);
}

TEST_F(TestArrayLambda, read_of_copy_at_sum)
{
  const BitwuzlaTerm *p   = byte_const("p");
  const BitwuzlaTerm *sum = term(BITWUZLA_KIND_BV_ADD, p, byte_const("q"));
  bitwuzla_assert(d_bzla, term(BITWUZLA_KIND_DISTINCT, sum, byte(0xff)));
  assert_copy_read_at(sum);
  ASSERT_EQ(bitwuzla_check_sat(d_bzla), BITWUZLA_SAT);
}

TEST_F(TestArrayLambda, read_of_copy_with_direct_read_of_source)
{
  const BitwuzlaTerm *p = byte_const("p");
  bitwuzla_assert(d_bzla, term(BITWUZLA_KIND_DISTINCT, p, byte(0xff)));
  bitwuzla_assert(d_bzla,
                  term(BITWUZLA_KIND_EQUAL,
                       term(BITWUZLA_KIND_ARRAY_SELECT,
                            written_constant_array(),
                            byte_const("s")),
                       byte_const("t")));
  assert_copy_read_at(p);
  ASSERT_EQ(bitwuzla_check_sat(d_bzla), BITWUZLA_SAT);
}

TEST_F(TestArrayLambda, read_of_copy_value_matches_model)
{
  const BitwuzlaTerm *p = byte_const("p");
  bitwuzla_assert(d_bzla, term(BITWUZLA_KIND_DISTINCT, p, byte(0xff)));
  const BitwuzlaTerm *read =
      term(BITWUZLA_KIND_APPLY,
           copy_overriding_last_index(written_constant_array()),
           p);
  assert_nonzero_read_back_from_free_array(read);
  ASSERT_EQ(bitwuzla_check_sat(d_bzla), BITWUZLA_SAT);
  std::string p_value =
      bitwuzla_get_bv_value(d_bzla, bitwuzla_get_value(d_bzla, p));
  std::string read_value =
      bitwuzla_get_bv_value(d_bzla, bitwuzla_get_value(d_bzla, read));
  ASSERT_EQ(read_value, p_value == "00000001" ? "00000010" : "00000000");
}

TEST_F(TestArrayLambda, store_over_lambda_over_stores_on_constant_array)
{
  const BitwuzlaSort *sort = bitwuzla_mk_array_sort(d_bzla, d_bv64, d_bv8);
  const BitwuzlaTerm *memory =
      stores_over(bitwuzla_mk_const_array(d_bzla, sort, byte(0)));
  const BitwuzlaTerm *i      = bitwuzla_mk_var(d_bzla, d_bv64, "i");
  const BitwuzlaTerm *lambda = term(
      BITWUZLA_KIND_LAMBDA, i, term(BITWUZLA_KIND_ARRAY_SELECT, memory, i));
  const BitwuzlaTerm *x = bitwuzla_mk_var(d_bzla, d_bv64, "x");
  const BitwuzlaTerm *stored =
      term(BITWUZLA_KIND_LAMBDA,
           x,
           term(BITWUZLA_KIND_ITE,
                term(BITWUZLA_KIND_EQUAL,
                     x,
                     bitwuzla_mk_bv_value_uint64(d_bzla, d_bv64, 100)),
                byte(0xaa),
                term(BITWUZLA_KIND_APPLY, lambda, x)));
  bitwuzla_assert(d_bzla,
                  term(BITWUZLA_KIND_EQUAL,
                       term(BITWUZLA_KIND_APPLY,
                            stored,
                            bitwuzla_mk_const(d_bzla, d_bv64, "index")),
                       byte(0xaa)));
  ASSERT_EQ(bitwuzla_check_sat(d_bzla), BITWUZLA_SAT);
}

TEST_F(TestArrayLambda, constant_array_depending_on_enclosing_lambda_index)
{
  const BitwuzlaSort *sort = bitwuzla_mk_array_sort(d_bzla, d_bv64, d_bv8);
  const BitwuzlaTerm *i    = bitwuzla_mk_var(d_bzla, d_bv64, "i");
  const BitwuzlaTerm *low_byte =
      bitwuzla_mk_term1_indexed2(d_bzla, BITWUZLA_KIND_BV_EXTRACT, i, 7, 0);
  const BitwuzlaTerm *memory =
      stores_over(bitwuzla_mk_const_array(d_bzla, sort, low_byte));
  const BitwuzlaTerm *lambda =
      term(BITWUZLA_KIND_LAMBDA,
           i,
           term(BITWUZLA_KIND_ARRAY_SELECT,
                memory,
                bitwuzla_mk_const(d_bzla, d_bv64, "index")));
  bitwuzla_assert(d_bzla,
                  term(BITWUZLA_KIND_EQUAL,
                       term(BITWUZLA_KIND_APPLY,
                            lambda,
                            bitwuzla_mk_const(d_bzla, d_bv64, "first")),
                       byte(5)));
  bitwuzla_assert(d_bzla,
                  term(BITWUZLA_KIND_EQUAL,
                       term(BITWUZLA_KIND_APPLY,
                            lambda,
                            bitwuzla_mk_const(d_bzla, d_bv64, "second")),
                       byte(6)));
  ASSERT_EQ(bitwuzla_check_sat(d_bzla), BITWUZLA_SAT);
}

TEST_F(
    TestArrayLambda,
    constant_array_depending_on_enclosing_lambda_index_stored_into_free_array)
{
  const BitwuzlaSort *sort = bitwuzla_mk_array_sort(d_bzla, d_bv64, d_bv8);
  const BitwuzlaTerm *i    = bitwuzla_mk_var(d_bzla, d_bv64, "i");
  const BitwuzlaTerm *low_byte =
      bitwuzla_mk_term1_indexed2(d_bzla, BITWUZLA_KIND_BV_EXTRACT, i, 7, 0);
  const BitwuzlaTerm *memory =
      stores_over(bitwuzla_mk_const_array(d_bzla, sort, low_byte));
  const BitwuzlaTerm *lambda =
      term(BITWUZLA_KIND_LAMBDA,
           i,
           term(BITWUZLA_KIND_ARRAY_SELECT,
                memory,
                bitwuzla_mk_const(d_bzla, d_bv64, "index")));
  const BitwuzlaTerm *out =
      term(BITWUZLA_KIND_ARRAY_STORE,
           term(BITWUZLA_KIND_ARRAY_STORE,
                bitwuzla_mk_const(d_bzla, d_array, "a"),
                byte(0),
                term(BITWUZLA_KIND_APPLY,
                     lambda,
                     bitwuzla_mk_const(d_bzla, d_bv64, "first"))),
           byte(1),
           term(BITWUZLA_KIND_APPLY,
                lambda,
                bitwuzla_mk_const(d_bzla, d_bv64, "second")));
  bitwuzla_assert(d_bzla,
                  term(BITWUZLA_KIND_EQUAL,
                       term(BITWUZLA_KIND_ARRAY_SELECT, out, byte_const("r")),
                       byte(5)));
  bitwuzla_assert(d_bzla,
                  term(BITWUZLA_KIND_EQUAL,
                       term(BITWUZLA_KIND_ARRAY_SELECT, out, byte_const("s")),
                       byte(6)));
  ASSERT_EQ(bitwuzla_check_sat(d_bzla), BITWUZLA_SAT);
}

TEST_F(TestArrayLambda, read_of_copy_at_stored_index_has_stored_value)
{
  const BitwuzlaTerm *p = byte_const("p");
  bitwuzla_assert(d_bzla, term(BITWUZLA_KIND_BV_UGT, p, byte(0)));
  bitwuzla_assert(d_bzla, term(BITWUZLA_KIND_BV_ULT, p, byte(2)));
  const BitwuzlaTerm *read =
      term(BITWUZLA_KIND_APPLY,
           copy_overriding_last_index(written_constant_array()),
           p);
  assert_nonzero_read_back_from_free_array(read);
  ASSERT_EQ(bitwuzla_check_sat(d_bzla), BITWUZLA_SAT);
  ASSERT_EQ(std::string(bitwuzla_get_bv_value(
                d_bzla, bitwuzla_get_value(d_bzla, read))),
            "00000010");
}
