from z3 import *
# from BitVector import BitVector
# Type = Datatype(f'Tuple({a.name()},{b.name()},{c.name()},{d.name()})')
# def Tuple(a, b, c, d):
    
#     Type = Datatype('Tuple')
#     Type.declare('mk', 
#                 ('first', BoolSort()), 
#                 ('second', BitVecSort(24)), 
#                 ('third', BitVecSort(8)), 
#                 ('fourth', BitVecSort(1))
#                  )
#     Type = Type.create()
#     return Type
    
# Tuple = Datatype('Tuple')
# Tuple.declare('mk', ('first', Bool()), ('second', BitVec()), ('third', BitVec()), ('fourth', BitVec()))
# Tuple = Tuple.create()

TupleType, mkTupleType, (first, second, third, fourth) = TupleSort('MyTuple', [BoolSort(), BitVecSort(25), BitVecSort(8), BitVecSort(1)])

opTuple, mkOpTuple, (op_first, op_second, op_third) = TupleSort('opTuple', [BitVecSort(24), BoolSort(), BitVecSort(1)])

normTuple, mkNormTuple, (norm_first, norm_second, norm_third) = TupleSort('opTuple', [BoolSort(), BitVecSort(8), BitVecSort(25)])

def fp_adder_exp_AgeqB(a_sign, b_sign, out_sign, a_exp, b_exp, out_exp, a_mant, b_mant, out_mant):
    constraint = True
    # print("a_mant size = ", a_mant.size())
    # print("b_mant size = ", b_mant.size())
    exp_diff = BitVec('exp_diff', 8)

    tmp_mant = BitVec('tmp_mant', 24)

    constraint = And(constraint, out_exp == a_exp)
    constraint = And(constraint, out_sign == a_sign)

    exp_diff_out, exp_diff_cons, _ = subtractor(a_exp, b_exp)
    constraint = And(constraint, exp_diff_cons)
    constraint = And(constraint, exp_diff == exp_diff_out)
    

    exp_diff_expand = BitVec('exp_diff_expand', 24)
    leading_zeros = BitVecVal(0, 16)
    exp_diff_expand = Concat(leading_zeros, exp_diff)
    constraint = And(constraint, exp_diff_expand == Concat(leading_zeros, exp_diff))

    constraint = And(constraint, tmp_mant == (b_mant >> exp_diff_expand))

    # tmp_mant_low = Extract(22, 0, tmp_mant)
    tmp_mant_low = Extract(23, 0, tmp_mant)

    mant_res = BitVec('mant_res', 25)
    mant_res_cons = Bool('mant_res_cons')
    cout = BitVec('cout', 1)
    # mant_tuple = mkOpTuple(mant_res, mant_res_cons, cout)
    mant_tuple = If(a_sign == b_sign, adder_tuple_wrapper(a_mant, tmp_mant_low), subtractor_tuple_wrapper(a_mant, tmp_mant_low))
    # print("mant_tuple size = ", op_first(mant_tuple).size())
    constraint = And(constraint, Extract(23, 0, mant_res) == op_first(mant_tuple))
    constraint = And(constraint, Extract(24, 24, mant_res) == op_third(mant_tuple))
    constraint = And(constraint, op_second(mant_tuple))
    # pad = BitVecVal(0, 1)
    # mant_res_final = BitVec('mant_res_final', 25)
    # constraint = And(constraint, mant_res_final == Concat(pad, mant_res))

    ret_tuple = mkTupleType(constraint, mant_res, out_exp, out_sign)

    return ret_tuple

    # return constraint, out_mant, out_exp, out_sign
    


def fp_adder_exp_BgeqA(a_sign, b_sign, out_sign, a_exp, b_exp, out_exp, a_mant, b_mant, out_mant):
    constraint = True

    exp_diff = BitVec('exp_diff', 8)

    tmp_mant = BitVec('tmp_mant', 24)

    constraint = And(constraint, out_exp == b_exp)
    constraint = And(constraint, out_sign == b_sign)

    exp_diff_out, exp_diff_cons, _ = subtractor(b_exp, a_exp)
    constraint = And(constraint, exp_diff == exp_diff_out)
    constraint = And(constraint, exp_diff_cons)

    exp_diff_expand = BitVec('exp_diff_expand', 24)
    leading_zeros = BitVecVal(0, 16)
    exp_diff_expand = Concat(leading_zeros, exp_diff)
    constraint = And(constraint, exp_diff_expand == Concat(leading_zeros, exp_diff))

    constraint = And(constraint, tmp_mant == (b_mant >> exp_diff_expand))

    tmp_mant_low = Extract(23, 0, tmp_mant)

    mant_res = BitVec('mant_res', 24)
    mant_res_cons = Bool('mant_res_cons')
    cout = BitVec('cout', 1)
    # mant_tuple = mkOpTuple(mant_res, mant_res_cons, cout)
    mant_tuple = If(a_sign == b_sign, adder_tuple_wrapper(b_mant, tmp_mant_low), subtractor_tuple_wrapper(b_mant, tmp_mant_low))
    
    constraint = And(constraint, Extract(22, 0, op_first(mant_tuple)) == Extract(22, 0, mant_res))
    # constraint = And(constraint, Extract(24, 24, op_third(mant_tuple)) == cout)
    constraint = And(constraint, op_second(mant_tuple))

    # constraint = And(constraint, Extract(23, 0, out_mant) == mant_res)
    # constraint = And(constraint, Extract(24, 24, out_mant) == cout)
    # constraint = And(constraint, mant_res_cons)

    # pad = BitVecVal(0, 1)
    # mant_res_final = BitVec('mant_res_final', 25)
    # constraint = And(constraint, mant_res_final == Concat(pad, mant_res))
    
    # Changing how the ret tuple is composed here somehow segfaults the code
    ret_tuple = mkTupleType(constraint, mant_res, out_exp, out_sign)

    # ret_tuple = mkTupleType(constraint, mant_res_final, out_exp, out_sign)
    return ret_tuple

    # return constraint, out_mant, out_exp, out_sign



def fp_adder_exp_eq_s_eq(a_sign, out_sign, a_exp, out_exp, a_mant, b_mant, out_mant):
    
    constraint = True

    add_out, add_cons, cout = adder(a_mant, b_mant)

    out_mant_low = Extract(23, 0, out_mant)

    constraint = And(constraint, add_cons)
    constraint = And(constraint, out_mant_low == add_out)
    constraint = And(constraint, out_sign == a_sign)
    constraint = And(constraint, out_exp == a_exp)

    out_mant_msb = Extract(24, 24, out_mant)
    constraint = And(constraint, out_mant_msb == 1)
    
    # return constraint, out_mant, out_exp, out_sign
    ret_tuple = mkTupleType(constraint, out_mant, out_exp, out_sign)

    return ret_tuple

def fp_adder_exp_eq_s_AgeqB(a_sign, out_sign, a_exp, out_exp, a_mant, b_mant, out_mant):

    constraint = True

    out_mant_low = Extract(23, 0, out_mant)

    sub_out, sub_cons, _ = subtractor(a_mant, b_mant)
    constraint = And(constraint, sub_cons)
    constraint = And(constraint, out_mant_low == sub_out)

    constraint = And(constraint, out_sign == a_sign)
    constraint = And(constraint, out_exp == a_exp)

    # print("constraint:", type(constraint))
    # print("out_mant:", type(out_mant))
    # print("out_exp:", type(out_exp))
    # print("out_sign:", type(out_sign))
    ret_tuple = mkTupleType(constraint, out_mant, out_exp, out_sign)


    return ret_tuple

def fp_adder_exp_eq_s_BgeqA(b_sign, out_sign, b_exp, out_exp, a_mant, b_mant, out_mant):

    constraint = True

    out_mant_low = Extract(23, 0, out_mant)

    sub_out, sub_cons, _ = subtractor(b_mant, a_mant)
    constraint = And(constraint, sub_cons)
    constraint = And(constraint, out_mant_low == sub_out)

    constraint = And(constraint, out_sign == b_sign)
    constraint = And(constraint, out_exp == b_exp)

    # print("constraint:", type(constraint))
    # print("out_mant:", type(out_mant))
    # print("out_exp:", type(out_exp))
    # print("out_sign:", type(out_sign))

    # return constraint, out_mant, out_exp, out_sign
    ret_tuple = mkTupleType(constraint, out_mant, out_exp, out_sign)

    return ret_tuple


def norm_sub_shift(in_exp, in_mant, num_lead_zeros):
    constraint = True

    out_exp = BitVec('out_exp', 8)
    out_mant = BitVec('out_mant', 25)

    
    # constrain inputs to only numbers that do not require rounding
    # dude did not put a rounder into his FPU so FPU is guaranteed failing on inputs that need to be rounded
    constraint = And(constraint, Extract(in_mant.size() - num_lead_zeros - 1, in_mant.size() - num_lead_zeros - 1 - 2, in_mant) < 0b100)
    constraint = And(constraint, out_mant == (in_mant >> num_lead_zeros))
    constraint = And(constraint, out_exp == (in_exp - num_lead_zeros))

    ret_tuple = mkNormTuple(constraint, out_exp, out_mant)

    return ret_tuple


def add_normaliser(in_exp, in_mant):

    constraint = True

    # If(Extract(23, _, in_mant) == 0 _, norm_sub_shift(in_exp, in_mant, _), _)
    print("in_mant.size = ", in_mant.size())

    normaliser_mant = BitVec('normaliser_mant', 25)
    normaliser_exp = BitVec('normaliser_exp', 8)

    norm_tuple = If(Extract(23, 3, in_mant) == 0b000000000000000000001, norm_sub_shift(in_exp, in_mant, 20), 
                                        If(Extract(23, 4, in_mant) == 0b00000000000000000001, norm_sub_shift(in_exp, in_mant, 19), 
                                           If(Extract(23, 5, in_mant) == 0b0000000000000000001, norm_sub_shift(in_exp, in_mant, 18), 
                                              If(Extract(23, 6, in_mant) == 0b000000000000000001, norm_sub_shift(in_exp, in_mant, 17), 
                                                 If(Extract(23, 7, in_mant) == 0b00000000000000001, norm_sub_shift(in_exp, in_mant, 16), 
                                                    If(Extract(23, 8, in_mant) == 0b0000000000000001, norm_sub_shift(in_exp, in_mant, 15), 
                                                       If(Extract(23, 9, in_mant) == 0b000000000000001, norm_sub_shift(in_exp, in_mant, 14), 
                                                          If(Extract(23, 10, in_mant) == 0b00000000000001, norm_sub_shift(in_exp, in_mant, 13), 
                                                             If(Extract(23, 11, in_mant) == 0b0000000000001, norm_sub_shift(in_exp, in_mant, 12), 
                                                                If(Extract(23, 12, in_mant) == 0b000000000001, norm_sub_shift(in_exp, in_mant, 11), 
                                                                   If(Extract(23, 13, in_mant) == 0b00000000001, norm_sub_shift(in_exp, in_mant, 10), 
                                                                      If(Extract(23, 14, in_mant) == 0b0000000001, norm_sub_shift(in_exp, in_mant, 9), 
                                                                         If(Extract(23, 15, in_mant) == 0b000000001, norm_sub_shift(in_exp, in_mant, 8), 
                                                                            If(Extract(23, 16, in_mant) == 0b00000001, norm_sub_shift(in_exp, in_mant, 7), 
                                                                               If(Extract(23, 17, in_mant) == 0b0000001, norm_sub_shift(in_exp, in_mant, 6), 
                                                                                  If(Extract(23, 18, in_mant) == 0b000001, norm_sub_shift(in_exp, in_mant, 5), 
                                                                                     If(Extract(23, 19, in_mant) == 0b00001, norm_sub_shift(in_exp, in_mant, 4), 
                                                                                        If(Extract(23, 20, in_mant) == 0b0001, norm_sub_shift(in_exp, in_mant, 3), 
                                                                                           If(Extract(23, 21, in_mant) == 0b001, norm_sub_shift(in_exp, in_mant, 2), 
                                                                                              If(Extract(23, 22, in_mant) == 0b01, norm_sub_shift(in_exp, in_mant, 1), 
                                                                                                 mkNormTuple(True, in_exp, in_mant)))))))))))))))))))))
    constraint = And(constraint, norm_first(norm_tuple))
    constraint = And(constraint, normaliser_exp == norm_second(norm_tuple))
    constraint = And(constraint, normaliser_mant == norm_third(norm_tuple))

    ret_tuple = mkNormTuple(constraint, normaliser_exp, normaliser_mant)

    return ret_tuple

    # ret_tuple = mkNormTuple(constraint, in_exp, in_mant)

    # return ret_tuple

def fp_sign_compare(a_sign, b_sign, out_sign, a_exp, b_exp, out_exp, a_mant_full, b_mant_full, out_mant):

    ret_constraint = Bool('ret_constraint')
    ret_mant = BitVec('ret_mant', 25)
    ret_exp = BitVec('ret_exp', 8)
    ret_sign = BitVec('ret_exp', 1)

    # ret_tuple = Tuple(ret_constraint, ret_mant, ret_exp, ret_sign)
    # ret_tuple = mkTupleType
    # ret_tuple = mkTupleType(ret_constraint, ret_mant, ret_exp, ret_sign)    

    if_tuple = If(a_sign == b_sign, fp_adder_exp_eq_s_eq(a_sign, out_sign, a_exp, out_exp, a_mant_full, b_mant_full, out_mant),  
                                                                                           fp_mant_compare(a_sign, b_sign, out_sign, a_exp, b_exp, out_exp, a_mant_full, b_mant_full, out_mant))
    # ret_tuple = Tuple(non_norm_constraint, non_norm_mant, non_norm_exp, non_norm_sign)

    constraint = first(if_tuple)
    constraint = And(constraint, ret_mant == second(if_tuple))
    constraint = And(constraint, ret_exp == third(if_tuple))
    constraint = And(constraint, ret_sign == fourth(if_tuple))

    ret_tuple = mkTupleType(constraint, ret_mant, ret_exp, ret_sign)  

    return ret_tuple
    # return non_norm_constraint, non_norm_mant, non_norm_exp, non_norm_sign 

# Issue: If cannot handle tuples in return statement
def fp_mant_compare(a_sign, b_sign, out_sign, a_exp, b_exp, out_exp, a_mant_full, b_mant_full, out_mant):
    
    ret_constraint = Bool('ret_constraint')
    ret_mant = BitVec('ret_mant', 25)
    ret_exp = BitVec('ret_exp', 8)
    ret_sign = BitVec('ret_exp', 1)

    # ret_tuple = mkTupleType(ret_constraint, ret_mant, ret_exp, ret_sign)   

    if_tuple = If(a_mant_full > b_mant_full, fp_adder_exp_eq_s_AgeqB(a_sign, out_sign, a_exp, out_exp, a_mant_full, b_mant_full, out_mant), 
                                                                                                    fp_adder_exp_eq_s_BgeqA(b_sign, out_sign, b_exp, out_exp, a_mant_full, b_mant_full, out_mant))
    # ret_tuple = Tuple(non_norm_constraint, non_norm_mant, non_norm_exp, non_norm_sign)

    constraint = first(if_tuple)
    constraint = And(constraint, ret_mant == second(if_tuple))
    constraint = And(constraint, ret_exp == third(if_tuple))
    constraint = And(constraint, ret_sign == fourth(if_tuple))
    # first(ret_tuple) = constraint

    ret_tuple = mkTupleType(constraint, ret_mant, ret_exp, ret_sign)  

    return ret_tuple
    # return non_norm_constraint, non_norm_mant, non_norm_exp, non_norm_sign              

def fp_exp_compare(a_sign, b_sign, non_norm_sign, a_exp, b_exp, non_norm_exp, a_mant_full, b_mant_full, non_norm_mant):

    constraint = True

    ret_constraint = Bool('ret_constraint')
    ret_mant = BitVec('ret_mant', 25)
    ret_exp = BitVec('ret_exp', 8)
    ret_sign = BitVec('ret_sign', 1)

    # ret_tuple = mkTupleType(ret_constraint, ret_mant, ret_exp, ret_sign)   

    if_tuple = If(a_exp > b_exp, fp_adder_exp_AgeqB(a_sign, b_sign, non_norm_sign, a_exp, b_exp, non_norm_exp, a_mant_full, b_mant_full, non_norm_mant), 
                                                                                        fp_adder_exp_BgeqA(a_sign, b_sign, non_norm_sign, a_exp, b_exp, non_norm_exp, a_mant_full, b_mant_full, non_norm_mant))
    
    constraint = And(constraint, first(if_tuple))
    constraint = And(constraint, ret_mant == second(if_tuple))
    constraint = And(constraint, ret_exp == third(if_tuple))
    constraint = And(constraint, ret_sign == fourth(if_tuple))
    # first(ret_tuple) = constraint

    ret_tuple = mkTupleType(constraint, ret_mant, ret_exp, ret_sign)  

    return ret_tuple
    # return non_norm_constraint, non_norm_mant, non_norm_exp, non_norm_sign



def handle_ovf(in_exp, in_mant):

    constraint = True

    in_mant_norm = BitVec('in_mant_norm', 25)
    in_exp_norm = BitVec('in_exp_norm', 8)

    out, add_cons, cout = adder(in_exp, BitVecVal(1, 8))

    constraint = And(constraint, add_cons)
    constraint = And(constraint, (in_exp_norm == out))

    constraint = And(constraint, (in_mant_norm == (in_mant >> 1)))

    return mkNormTuple(constraint, in_exp_norm, in_mant_norm)



def fp_adder(a, b):

    assert(a.size() == b.size())

    constraint = True

    out = BitVec('out', 32)

    out_mant = BitVec('out', 25)

    out_sign = BitVec('out_sign', 1)
    constraint = And(constraint, out_sign == Extract(31, 31, out))
    # out_sign = Extract(31, 31, out)

    out_exp = BitVec('out_exp', 8)
    constraint = And(constraint, out_exp == Extract(30, 23, out))

    out_mant_final = BitVec('out_mant_final', 23)
    constraint = And(constraint, out_mant_final == Extract(22, 0, out))
    # out_mant_final = Extract(22, 0, out_mant)

    a_sign = BitVec('a_sign', 1) 
    constraint = And(constraint, a_sign == Extract(31, 31, a))
    a_exp = BitVec('a_exp', 8) 
    constraint = And(constraint, a_exp == Extract(30, 23, a))
    a_mant = BitVec('a_mant', 23) 
    constraint = And(constraint, a_mant == Extract(22, 0, a))

    b_sign = BitVec('b_sign', 1) 
    constraint = And(constraint, b_sign == Extract(31, 31, b))
    b_exp = BitVec('b_exp', 8) 
    constraint = And(constraint, b_exp == Extract(30, 23, b))
    b_mant = BitVec('b_mant', 23) 
    constraint = And(constraint, b_mant == Extract(22, 0, b))

    hidden_bit = BitVec('hidden_bit', 1)
    constraint = And(constraint, (hidden_bit == 1))

    a_mant_full = BitVec('a_mant_full', 24)
    b_mant_full = BitVec('b_mant_full', 24)

    # a_mant_full = Concat(hidden_bit, a_mant)
    # b_mant_full = Concat(hidden_bit, b_mant)
    # print("a_mant_full.size = ", a_mant_full.size())
    # print("b_mant_full.size = ", b_mant_full.size())

    constraint = And(constraint, (a_mant_full == Concat(hidden_bit, a_mant)))
    constraint = And(constraint, (b_mant_full == Concat(hidden_bit, b_mant)))

    # non_norm_constraint = Bool('non_norm_constraint')
    non_norm_constraint = Bool('non_norm_constraint')
    non_norm_mant = BitVec('non_norm_mant', 25)
    non_norm_exp = BitVec('non_norm_exp', 8)
    non_norm_sign = BitVec('non_norm_exp', 1)

    # non_norm_tuple = Tuple(non_norm_constraint, non_norm_mant, non_norm_exp, non_norm_sign)
    # non_norm_tuple = mkTupleType(non_norm_constraint, non_norm_mant, non_norm_exp, non_norm_sign)   

    non_norm_tuple = If(a_exp == b_exp, fp_sign_compare(a_sign, b_sign, out_sign, a_exp, b_exp, out_exp, a_mant_full, b_mant_full, out_mant), fp_exp_compare(a_sign, b_sign, non_norm_sign, a_exp, b_exp, non_norm_exp, a_mant_full, b_mant_full, non_norm_mant))
                                                        # exponents not same function in remaining case
    
    constraint = And(constraint, first(non_norm_tuple))
    constraint = And(constraint, (non_norm_mant == second(non_norm_tuple)))
    constraint = And(constraint, (non_norm_exp == third(non_norm_tuple)))
    constraint = And(constraint, (out_sign == fourth(non_norm_tuple)))
    
    # constraint = And(constraint, non_norm_constraint)
    # constraint = And(constraint, (out_sign == non_norm_constraint))
    ovf_mant = BitVec('ovf_mant', 25)
    ovf_exp = BitVec('ovf_exp', 8)
    # ovf_sign = BitVec('ovf_exp', 1)

    ovf_tuple = If(Extract(24, 24, out_mant) == 1, handle_ovf(third(non_norm_tuple), second(non_norm_tuple)), mkNormTuple(True, third(non_norm_tuple), second(non_norm_tuple)))
    # norm_cons, norm_exp, norm_mant = adder(non_norm_exp, non_norm_mant)

    constraint = And(constraint, norm_first(ovf_tuple))
    constraint = And(constraint, ovf_exp == norm_second(ovf_tuple))
    constraint = And(constraint, ovf_mant == norm_third(ovf_tuple))

    # constraint = And(constraint, out_exp == norm_exp)
    # constraint = And(constraint, out_mant == norm_mant)

    final_norm_tuple = add_normaliser(norm_second(ovf_tuple), norm_third(ovf_tuple))

    constraint = And(constraint, norm_first(final_norm_tuple))
    constraint = And(constraint, out_exp == norm_second(final_norm_tuple))
    constraint = And(constraint, out_mant_final == Extract(22, 0, norm_third(final_norm_tuple)))

    return out, constraint

# out = a - b
def subtractor_tuple_wrapper(a, b):

    constraint = True

    sub_tuple_out = BitVec('sub_out_tuple', a.size())
    # sub_tuple_cout = BitVec('sub_cout_tuple', 1)
    
    out, sub_constraint, throwaway = subtractor(a, b)

    constraint = And(constraint, sub_constraint)
    constraint = And(constraint, sub_tuple_out == out)

    ret_tuple = mkOpTuple(sub_tuple_out, constraint, throwaway)

    return ret_tuple


# out = a - b
def subtractor(a, b):

    constraint = True

    assert(a.size() == b.size())
    sub_out = BitVec('sub_out', a.size())

    throwaway = BitVecVal(0, 1)

    borrow_in = BitVec('carry_out', a.size() + 1)

    constraint = And(constraint, (Extract(0, 0, borrow_in) == 0))

    for i in range(a.size()):
        out_bit = Extract(i, i, sub_out)
        a_bit = Extract(i, i, a)
        b_bit = Extract(i, i, b)
        borrow_in_curr = Extract(i, i, borrow_in)
        borrow_in_next = Extract(i+1, i+1, borrow_in)

        
        constraint = And(constraint, (out_bit == a_bit ^ b_bit ^ borrow_in_curr))
        constraint = And(constraint, (borrow_in_next == (~(a_bit ^ b_bit)) & borrow_in_curr | ((~a_bit) & b_bit)))

    return sub_out, constraint, throwaway


def adder_tuple_wrapper(a, b):

    constraint = True

    add_tuple_out = BitVec('add_out_tuple', a.size())
    # add_constraint_tuple = True
    add_tuple_cout = BitVec('add_cout_tuple', 1)
    
    out, add_constraint, cout = adder(a, b)

    constraint = And(constraint, add_constraint)
    constraint = And(constraint, add_tuple_out == out)
    constraint = And(constraint, add_tuple_cout == cout)
    ret_tuple = mkOpTuple(add_tuple_out, constraint, add_tuple_cout)

    return ret_tuple

def adder(a, b):

    constraint = True

    assert(a.size() == b.size())
    add_out = BitVec('add_out', a.size())

    carry_out = BitVec('carry_out', a.size()+1)

    constraint = And(constraint, (Extract(0, 0, carry_out) == 0))

    for i in range(a.size()):
        out_bit = Extract(i, i, add_out)
        a_bit = Extract(i, i, a)
        b_bit = Extract(i, i, b)
        carry_out_bit_curr = Extract(i, i, carry_out)
        carry_out_bit_next = Extract(i+1, i+1, carry_out)

        
        constraint = And(constraint, (out_bit == a_bit ^ b_bit ^ carry_out_bit_curr))
        constraint = And(constraint, (carry_out_bit_next == (a_bit & b_bit) | ((a_bit ^ b_bit) & carry_out_bit_curr)))

    return add_out, constraint, Extract(a.size(), a.size(), carry_out)


def main():
    

    a = BitVec('a', 32)
    b = BitVec('b', 32)

    return fp_adder(a, b)
    # return subtractor(a, b)
    # return adder(a, b)
    
    print('testing commit')

if __name__ == "__main__":

    # a = BitVec('a', 23)
    # b = BitVec('b', 23)

    # out, constraint = main()

    a_float = FP('a_float', Float32())
    b_float = FP('b_float', Float32())

    a = BitVec('a', 32)
    b = BitVec('b', 32)

    nan = Float32()
    inf = Float32()
    neg_inf = Float32()

    val_constraint = (a_float != fpNaN(nan)) 
    val_constraint = And(val_constraint, a_float != fpPlusInfinity(inf)) 
    val_constraint = And(val_constraint, a_float != fpMinusInfinity(neg_inf)) 

    val_constraint = (b_float != fpNaN(nan)) 
    val_constraint = And(val_constraint, b_float != fpPlusInfinity(inf)) 
    val_constraint = And(val_constraint, b_float != fpMinusInfinity(neg_inf))

    val_constraint = And(val_constraint, fpIsNormal(a_float) == True)
    val_constraint = And(val_constraint, fpIsNormal(b_float) == True)

    val_constraint = And(val_constraint, fpToFP(a, Float32()) == a_float)
    val_constraint = And(val_constraint, fpToFP(b, Float32()) == b_float)

    # dut_out = BitVec('dut_out', 32)
    
    dut_out, dut_constraint = fp_adder(a, b)

    solver = Solver()
    # solver.add(dut_out == out)
    solver.add(val_constraint)
    solver.add(dut_constraint)
    # converted_out = Float32()
    # solver.add(converted_out == fpToFP(dut_out, Float32()))
    converted_out = fpToFP(dut_out, Float32())
    actual_val = FP('actual_val', Float32())
    solver.add(actual_val == (a_float + b_float))
    solver.add(converted_out != actual_val)
    if solver.check() == sat:
        print("Solution: ", solver.model())
    else:
        print("No solution found")


