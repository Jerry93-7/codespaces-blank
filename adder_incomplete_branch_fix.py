from z3 import *


TupleType, mkTupleType, (get_cons, get_mant, get_exp, get_sign) = TupleSort('MyTuple', [BoolSort(), BitVecSort(25), BitVecSort(8), BitVecSort(1)])

opTuple, mkOpTuple, (op_get_res, op_get_cons, op_get_sign) = TupleSort('OpTuple', [BitVecSort(24), BoolSort(), BitVecSort(1)])

normTuple, mkNormTuple, (norm_get_cons, norm_get_exp, norm_get_mant) = TupleSort('NormTuple', [BoolSort(), BitVecSort(8), BitVecSort(25)])

# case where A has greater exponent than B
def fp_adder_exp_AgeqB(a_sign, b_sign, a_exp, b_exp, a_mant, b_mant):
    constraint = True
    exp_diff_AgeqB = BitVec('exp_diff_AgeqB', 8)

    tmp_mant = BitVec('tmp_mant', 24)

    res_sign = BitVec('res_sign', 1)
    res_exp = BitVec('res_exp', 8)
    res_mant = BitVec('res_mant', 25)

    # set output sign and exponent to a's sign and exponent
    constraint = And(constraint, res_sign == a_sign)
    constraint = And(constraint, res_exp == a_exp)
    
    # get difference between exponents
    exp_diff_out, exp_diff_cons, _ = subtractor(a_exp, b_exp)
    constraint = And(constraint, exp_diff_cons)
    constraint = And(constraint, exp_diff_AgeqB == exp_diff_out)
    
    # concatenate 16 0's to make difference a 24 bit number as 
    # Z3Py can only perform bitvec operations on bitvecs of same length
    exp_diff_expand = BitVec('exp_diff_expand', 24)
    leading_zeros = BitVecVal(0, 16)
    constraint = And(constraint, exp_diff_expand == Concat(leading_zeros, exp_diff_AgeqB))

    # shift b's mantissa by difference between exponents
    constraint = And(constraint, tmp_mant == LShR(b_mant, exp_diff_expand))

    mant_tuple = If(a_sign == b_sign, adder_tuple_wrapper(a_mant, tmp_mant), subtractor_tuple_wrapper(a_mant, tmp_mant))

    # create return tuple to return multiple values from a Z3Py If 
    constraint = And(constraint, Extract(23, 0, res_mant) == op_get_res(mant_tuple))
    constraint = And(constraint, Extract(24, 24, res_mant) == op_get_sign(mant_tuple))
    constraint = And(constraint, op_get_cons(mant_tuple))

    ret_tuple = mkTupleType(constraint, res_mant, res_exp, res_sign)
    return ret_tuple

    
# case where B has greater exponent than A
def fp_adder_exp_BgeqA(a_sign, b_sign, a_exp, b_exp, a_mant, b_mant):
    constraint = True

    exp_diff_BgeqA = BitVec('exp_diff_BgeqA', 8)

    tmp_mant = BitVec('tmp_mant', 24)

    res_sign = BitVec('res_sign', 1)
    res_exp = BitVec('res_exp', 8)
    res_mant = BitVec('res_mant', 25)

    # set output sign and exponent to b's sign and exponent
    constraint = And(constraint, res_exp == b_exp)
    constraint = And(constraint, res_sign == b_sign)

    # get difference between exponents
    exp_diff_out, exp_diff_cons, _ = subtractor(b_exp, a_exp)
    constraint = And(constraint, exp_diff_BgeqA == exp_diff_out)
    constraint = And(constraint, exp_diff_cons)

    # concatenate 16 0's to make difference a 24 bit number as 
    # Z3Py can only perform bitvec operations on bitvecs of same length
    exp_diff_expand = BitVec('exp_diff_expand', 24)
    leading_zeros = BitVecVal(0, 16)
    exp_diff_expand = Concat(leading_zeros, exp_diff_BgeqA)
    constraint = And(constraint, exp_diff_expand == Concat(leading_zeros, exp_diff_BgeqA))

    # shift a's mantissa by difference between exponents
    constraint = And(constraint, tmp_mant == LShR(a_mant, exp_diff_expand))

    mant_tuple = If(a_sign == b_sign, adder_tuple_wrapper(b_mant, tmp_mant), subtractor_tuple_wrapper(b_mant, tmp_mant))

    # create return tuple to return multiple values from a Z3Py If 
    constraint = And(constraint, op_get_res(mant_tuple) == Extract(23, 0, res_mant)) # op_get_res(mant_tuple)
    constraint = And(constraint, op_get_sign(mant_tuple) == Extract(24, 24, res_mant))
    constraint = And(constraint, op_get_cons(mant_tuple))

    ret_tuple = mkTupleType(constraint, res_mant, res_exp, res_sign)

    return ret_tuple


# case where exponents equal and signs equal
def fp_adder_exp_eq_s_eq(a_sign, a_exp, a_mant, b_mant):
    
    constraint = True

    # add mantissas
    add_out, add_cons, cout = adder(a_mant, b_mant)

    res_mant = BitVec('res_mant', 25)
    res_exp = BitVec('res_exp', 8)
    res_sign = BitVec('res_sign', 1)

    constraint = And(constraint, add_cons)
    constraint = And(constraint, Extract(23, 0, res_mant) == add_out)
    constraint = And(constraint, res_sign == a_sign)
    constraint = And(constraint, res_exp == a_exp)

    # make sure carryout is in the mantissa
    constraint = And(constraint, Extract(24, 24, res_mant) == 1)
    
    ret_tuple = mkTupleType(constraint, res_mant, res_exp, res_sign)

    return ret_tuple


# case where exponents equal, signs unequal, and A mantissa > B mantissa
def fp_adder_exp_eq_s_AgeqB(a_sign, a_exp, a_mant, b_mant):

    constraint = True


    res_mant = BitVec('res_mant', 25)
    res_exp = BitVec('res_exp', 8)
    res_sign = BitVec('res_sign', 1)

    sub_out, sub_cons, borrow_in_next = subtractor(a_mant, b_mant)
    constraint = And(constraint, sub_cons)
    constraint = And(constraint, Extract(23, 0, res_mant) == sub_out)
    constraint = And(constraint, Extract(24, 24, res_mant) == borrow_in_next)

    # set sign and exponent to sign and exponent of input that is larger
    constraint = And(constraint, res_sign == a_sign)
    constraint = And(constraint, res_exp == a_exp)

    ret_tuple = mkTupleType(constraint, res_mant, res_exp, res_sign)

    return ret_tuple


# case where exponents equal, signs unequal, and B mantissa > A mantissa
def fp_adder_exp_eq_s_BgeqA(b_sign, b_exp, a_mant, b_mant):

    constraint = True

    res_mant = BitVec('res_mant', 25)
    res_exp = BitVec('res_exp', 8)
    res_sign = BitVec('res_sign', 1)

    sub_out, sub_cons, borrow_in_next = subtractor(b_mant, a_mant)
    constraint = And(constraint, sub_cons)
    constraint = And(constraint, Extract(23, 0, res_mant) == sub_out)
    constraint = And(constraint, Extract(24, 24, res_mant) == borrow_in_next)

    # set sign and exponent to sign and exponent of input that is larger
    constraint = And(constraint, res_sign == b_sign)
    constraint = And(constraint, res_exp == b_exp)

    ret_tuple = mkTupleType(constraint, res_mant, res_exp, res_sign)

    return ret_tuple

# helper function to handle subtraction and right shifting for normalization
# use normal Z3Py bitvec subtraction because we do not have extra bit to hold
# carryout in verilog code when doing add/sub on exponents
def norm_sub_shift(in_exp, in_mant, num_lead_zeros):
    constraint = True

    norm_exp = BitVec('norm_exp', 8)
    norm_mant = BitVec('norm_mant', 25)

    lead_zeros_mant_width = BitVec('lead_zeros_mant_width', 25)
    lead_zeros_exp_width = BitVec('lead_zeros_exp_width', 8)

    constraint = And(constraint, (lead_zeros_mant_width == BitVecVal(num_lead_zeros, 25)))
    constraint = And(constraint, (lead_zeros_exp_width == BitVecVal(num_lead_zeros, 8)))

    constraint = And(constraint, norm_mant == (in_mant << lead_zeros_mant_width))
    # subtract here because designer does not account for overflow when 
    # performing operations on exponents
    constraint = And(constraint, norm_exp == (in_exp - lead_zeros_exp_width))

    ret_tuple = mkNormTuple(constraint, norm_exp, norm_mant)

    return ret_tuple


# models the "addition_normaliser" module in verilog
def add_normaliser(in_exp, in_mant):

    constraint = True

    print("in_mant.size = ", in_mant.size())

    normaliser_mant = BitVec('normaliser_mant', 25)
    normaliser_exp = BitVec('normaliser_exp', 8)


    norm_tuple = If(Extract(23, 0, in_mant) == BitVecVal(0b000000000000000000000001, 24), norm_sub_shift(in_exp, in_mant, 23),
                            If(Extract(23, 1, in_mant) == BitVecVal(0b00000000000000000000001, 23), norm_sub_shift(in_exp, in_mant, 22),
                                If(Extract(23, 2, in_mant) == BitVecVal(0b0000000000000000000001, 22), norm_sub_shift(in_exp, in_mant, 21),
                                    If(Extract(23, 3, in_mant) == BitVecVal(0b000000000000000000001, 21), norm_sub_shift(in_exp, in_mant, 20),
                                        If(Extract(23, 4, in_mant) == BitVecVal(0b00000000000000000001, 20), norm_sub_shift(in_exp, in_mant, 19), 
                                           If(Extract(23, 5, in_mant) == BitVecVal(0b0000000000000000001, 19), norm_sub_shift(in_exp, in_mant, 18), 
                                              If(Extract(23, 6, in_mant) == BitVecVal(0b000000000000000001, 18), norm_sub_shift(in_exp, in_mant, 17), 
                                                 If(Extract(23, 7, in_mant) == BitVecVal(0b00000000000000001, 17), norm_sub_shift(in_exp, in_mant, 16), 
                                                    If(Extract(23, 8, in_mant) == BitVecVal(0b0000000000000001, 16), norm_sub_shift(in_exp, in_mant, 15), 
                                                       If(Extract(23, 9, in_mant) == BitVecVal(0b000000000000001, 15), norm_sub_shift(in_exp, in_mant, 14), 
                                                          If(Extract(23, 10, in_mant) == BitVecVal(0b00000000000001, 14), norm_sub_shift(in_exp, in_mant, 13), 
                                                             If(Extract(23, 11, in_mant) == BitVecVal(0b0000000000001, 13), norm_sub_shift(in_exp, in_mant, 12), 
                                                                If(Extract(23, 12, in_mant) == BitVecVal(0b000000000001, 12), norm_sub_shift(in_exp, in_mant, 11), 
                                                                   If(Extract(23, 13, in_mant) == BitVecVal(0b00000000001, 11), norm_sub_shift(in_exp, in_mant, 10), 
                                                                      If(Extract(23, 14, in_mant) == BitVecVal(0b0000000001, 10), norm_sub_shift(in_exp, in_mant, 9), 
                                                                         If(Extract(23, 15, in_mant) == BitVecVal(0b000000001, 9), norm_sub_shift(in_exp, in_mant, 8), 
                                                                            If(Extract(23, 16, in_mant) == BitVecVal(0b00000001, 8), norm_sub_shift(in_exp, in_mant, 7), 
                                                                               If(Extract(23, 17, in_mant) == BitVecVal(0b0000001, 7), norm_sub_shift(in_exp, in_mant, 6), 
                                                                                  If(Extract(23, 18, in_mant) == BitVecVal(0b000001, 6), norm_sub_shift(in_exp, in_mant, 5), 
                                                                                     If(Extract(23, 19, in_mant) == BitVecVal(0b00001, 5), norm_sub_shift(in_exp, in_mant, 4), 
                                                                                        If(Extract(23, 20, in_mant) == BitVecVal(0b0001, 4), norm_sub_shift(in_exp, in_mant, 3), 
                                                                                           If(Extract(23, 21, in_mant) == BitVecVal(0b001, 3), norm_sub_shift(in_exp, in_mant, 2), 
                                                                                              If(Extract(23, 22, in_mant) == BitVecVal(0b01, 2), norm_sub_shift(in_exp, in_mant, 1), 
                                                                                                 mkNormTuple(True, BitVecVal(-1, 8), BitVecVal(-1, 8)))))))))))))))))))))))))
    constraint = And(constraint, norm_get_cons(norm_tuple))
    constraint = And(constraint, normaliser_exp == norm_get_exp(norm_tuple))
    constraint = And(constraint, normaliser_mant == norm_get_mant(norm_tuple))

    ret_tuple = mkNormTuple(constraint, normaliser_exp, normaliser_mant)

    return ret_tuple


# helper function for if signs are equal
def fp_sign_compare(a_sign, b_sign, a_exp, b_exp, a_mant_full, b_mant_full):


    ret_mant = BitVec('ret_mant', 25)
    ret_exp = BitVec('ret_exp', 8)
    ret_sign = BitVec('ret_exp', 1)
 

    if_tuple = If(a_sign == b_sign, fp_adder_exp_eq_s_eq(a_sign, a_exp, a_mant_full, b_mant_full),  
                                    fp_mant_compare(a_sign, b_sign, a_exp, b_exp, a_mant_full, b_mant_full))

    constraint = get_cons(if_tuple)
    constraint = And(constraint, ret_mant == get_mant(if_tuple))
    constraint = And(constraint, ret_exp == get_exp(if_tuple))
    constraint = And(constraint, ret_sign == get_sign(if_tuple))

    ret_tuple = mkTupleType(constraint, ret_mant, ret_exp, ret_sign)  

    return ret_tuple


# handles the mantissa comparison when input exponents are equal, but input signs are unequal
def fp_mant_compare(a_sign, b_sign, a_exp, b_exp, a_mant_full, b_mant_full):
    
    ret_mant = BitVec('ret_mant', 25)
    ret_exp = BitVec('ret_exp', 8)
    ret_sign = BitVec('ret_exp', 1)

    if_tuple = If(a_mant_full > b_mant_full, fp_adder_exp_eq_s_AgeqB(a_sign, a_exp, a_mant_full, b_mant_full), 
                                             fp_adder_exp_eq_s_BgeqA(b_sign, b_exp, a_mant_full, b_mant_full))


    constraint = get_cons(if_tuple)
    constraint = And(constraint, ret_mant == get_mant(if_tuple))
    constraint = And(constraint, ret_exp == get_exp(if_tuple))
    constraint = And(constraint, ret_sign == get_sign(if_tuple))


    ret_tuple = mkTupleType(constraint, ret_mant, ret_exp, ret_sign)  

    return ret_tuple
          

# handles comparison when input exponents not equal
def fp_exp_compare(a_sign, b_sign, a_exp, b_exp, a_mant_full, b_mant_full):

    constraint = True

    ret_mant = BitVec('ret_mant', 25)
    ret_exp = BitVec('ret_exp', 8)
    ret_sign = BitVec('ret_sign', 1)
 
    if_tuple = If(a_exp > b_exp, fp_adder_exp_AgeqB(a_sign, b_sign, a_exp, b_exp, a_mant_full, b_mant_full), 
                                 fp_adder_exp_BgeqA(a_sign, b_sign, a_exp, b_exp, a_mant_full, b_mant_full))
    
    constraint = And(constraint, get_cons(if_tuple))
    constraint = And(constraint, ret_mant == get_mant(if_tuple))
    constraint = And(constraint, ret_exp == get_exp(if_tuple))
    constraint = And(constraint, ret_sign == get_sign(if_tuple))

    ret_tuple = mkTupleType(constraint, ret_mant, ret_exp, ret_sign)  

    return ret_tuple



# performs the normalization when overflow in mantissa detected
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

    out_mant = BitVec('out_mant', 25)

    out_sign = BitVec('out_sign', 1)
    constraint = And(constraint, out_sign == Extract(31, 31, out))

    out_exp = BitVec('out_exp', 8)
    constraint = And(constraint, out_exp == Extract(30, 23, out))

    out_mant_final = BitVec('out_mant_final', 23)
    constraint = And(constraint, out_mant_final == Extract(22, 0, out))

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
    constraint = And(constraint, (a_mant_full == Concat(hidden_bit, a_mant)))
    constraint = And(constraint, (b_mant_full == Concat(hidden_bit, b_mant)))

    non_norm_mant = BitVec('non_norm_mant', 25)
    non_norm_exp = BitVec('non_norm_exp', 8)

    non_norm_tuple = If(a_exp == b_exp, fp_sign_compare(a_sign, b_sign, a_exp, b_exp, a_mant_full, b_mant_full), 
                                        fp_exp_compare(a_sign, b_sign, a_exp, b_exp, a_mant_full, b_mant_full))
                   
    constraint = And(constraint, get_cons(non_norm_tuple))
    constraint = And(constraint, (non_norm_mant == get_mant(non_norm_tuple)))
    constraint = And(constraint, (non_norm_exp == get_exp(non_norm_tuple)))
    constraint = And(constraint, (out_sign == get_sign(non_norm_tuple)))

    ovf_mant = BitVec('ovf_mant', 25)
    ovf_exp = BitVec('ovf_exp', 8)

    ovf_tuple = If(Extract(24, 24, out_mant) == 1, handle_ovf(get_exp(non_norm_tuple), get_mant(non_norm_tuple)), mkNormTuple(True, get_exp(non_norm_tuple), get_mant(non_norm_tuple)))

    constraint = And(constraint, norm_get_cons(ovf_tuple))
    constraint = And(constraint, ovf_exp == norm_get_exp(ovf_tuple))
    constraint = And(constraint, ovf_mant == norm_get_mant(ovf_tuple))

    final_norm_tuple = add_normaliser(ovf_exp, ovf_mant)

    constraint = And(constraint, norm_get_cons(final_norm_tuple))
    constraint = And(constraint, out_exp == norm_get_exp(final_norm_tuple))
    constraint = And(constraint, out_mant_final == Extract(22, 0, norm_get_mant(final_norm_tuple)))

    return out, constraint



# out = a - b
def subtractor_tuple_wrapper(a, b):

    constraint = True

    sub_tuple_out = BitVec('sub_out_tuple', a.size())
    
    out, sub_constraint, borrow_in_next = subtractor(a, b)

    constraint = And(constraint, sub_constraint)
    constraint = And(constraint, sub_tuple_out == out)

    ret_tuple = mkOpTuple(sub_tuple_out, constraint, borrow_in_next)

    return ret_tuple


# subtractor function for the borrow_out
# out = a - b
def subtractor(a, b):

    constraint = True

    assert(a.size() == b.size())
    sub_out = BitVec('sub_out', a.size())

    borrow_in_next = BitVecVal(0, 1)

    borrow_in = BitVec('borrow_in', a.size() + 1)

    constraint = And(constraint, (Extract(0, 0, borrow_in) == 0))

    for i in range(a.size()):
        out_bit = Extract(i, i, sub_out)
        a_bit = Extract(i, i, a)
        b_bit = Extract(i, i, b)
        borrow_in_curr = Extract(i, i, borrow_in)
        borrow_in_next = Extract(i+1, i+1, borrow_in)

        
        constraint = And(constraint, (out_bit == ((a_bit ^ b_bit) ^ borrow_in_curr)))
        constraint = And(constraint, (borrow_in_next == ((~(a_bit ^ b_bit)) & borrow_in_curr) | ((~a_bit) & b_bit)))

    return sub_out, constraint, borrow_in_next



def adder_tuple_wrapper(a, b):

    constraint = True

    add_tuple_out = BitVec('add_out_tuple', a.size())

    add_tuple_cout = BitVec('add_cout_tuple', 1)
    
    out, add_constraint, cout = adder(a, b)

    constraint = And(constraint, add_constraint)
    constraint = And(constraint, add_tuple_out == out)
    constraint = And(constraint, add_tuple_cout == cout)
    ret_tuple = mkOpTuple(add_tuple_out, constraint, add_tuple_cout)

    return ret_tuple


# adder function for the carry out
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

    sub_out = BitVec('sub_out', 32)
    
    out, constraint, borrow_in_next = subtractor(a, b)

    a_check = BitVec('a_check', 32)
    b_check = BitVec('b_check', 32)

    solver = Solver()
    constraint = And(constraint, sub_out == out)
    constraint = And(constraint, a_check == a)
    constraint = And(constraint, b_check == b)
    solver.add(constraint)
    solver.add(out != (a_check - b_check))

    if solver.check() == sat:
        print("Solution: ", solver.model())
    else:
        print("No solution found")

    return



if __name__ == "__main__":


    val_constraint = True
    a_float = FP('a_float', Float32())
    b_float = FP('b_float', Float32())

    a = BitVec('a', 32)
    b = BitVec('b', 32)

    # constraining values to the values that Z3Py spit out at me
    # when I first found this bug on a previous buggy version of FPU model
    a_test = BitVecVal(0b11000000000000000100100010000010, 32)
    b_test = BitVecVal(0b01000000000000000100100001111100, 32)

    val_constraint = And(val_constraint, a == a_test)
    val_constraint = And(val_constraint, b == b_test)

    # not considering special values and denormal numbers
    nan = Float32()
    inf = Float32()
    neg_inf = Float32()
 
    val_constraint = And(val_constraint, a_float != fpNaN(nan))
    val_constraint = And(val_constraint, a_float != fpPlusInfinity(inf)) 
    val_constraint = And(val_constraint, a_float != fpMinusInfinity(neg_inf)) 

    val_constraint = And(val_constraint, b_float != fpNaN(nan)) 
    val_constraint = And(val_constraint, b_float != fpPlusInfinity(inf)) 
    val_constraint = And(val_constraint, b_float != fpMinusInfinity(neg_inf))

    val_constraint = And(val_constraint, fpIsNormal(a_float) == True)
    val_constraint = And(val_constraint, fpIsNormal(b_float) == True)

    val_constraint = And(val_constraint, fpToFP(a, Float32()) == a_float)
    val_constraint = And(val_constraint, fpToFP(b, Float32()) == b_float)
    
    dut_out, dut_constraint = fp_adder(a, b)

    solver = Solver()

    solver.add(val_constraint)
    solver.add(dut_constraint)

    converted_out = fpToFP(dut_out, Float32())
    actual_val = FP('actual_val', Float32())
    solver.add(actual_val == (a_float + b_float))
    solver.add(converted_out != actual_val)
    if solver.check() == sat:
        print("Solution: ", solver.model())
    else:
        print("No solution found")

