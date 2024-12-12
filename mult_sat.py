from z3 import *

ovfTuple, mkOvfTuple, (get_ovf_tuple_cons, get_ovf_tuple_exp, get_ovf_tuple_prod) = TupleSort('ovfTuple', [BoolSort(), BitVecSort(8), BitVecSort(48)])

normTuple, mkNormTuple, (get_norm_cons, get_norm_exp, get_norm_prod) = TupleSort('NormTuple', [BoolSort(), BitVecSort(8), BitVecSort(48)])


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


def handle_ovf(in_exp, in_mant):

    constraint = True

    in_prod_norm = BitVec('in_prod_norm', 48)
    in_exp_norm = BitVec('in_exp_norm', 8)

    out, add_cons, cout = adder(in_exp, BitVecVal(1, 8))

    constraint = And(constraint, add_cons)
    constraint = And(constraint, (in_exp_norm == out))

    constraint = And(constraint, (in_prod_norm == (in_mant >> 1)))

    return mkOvfTuple(constraint, in_exp_norm, in_prod_norm)



def fp_multiplier(a, b):

    constraint = True

    out_mant = BitVec("out_mant", 25)
    out = BitVec('out', 32)

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

    constraint = And(constraint, out_sign == a_sign ^ b_sign)

    pre_ovf_exp = BitVec("pre_ovf_exp", 8)
    constraint = And(constraint, pre_ovf_exp == (a_exp + b_exp - BitVecVal(127, 8)))

    prod = BitVec("prod", 48)
    mult_res, mult_cons = bitwise_mult(a_mant_full, b_mant_full)
    constraint = And(constraint, mult_cons)
    constraint = And(constraint, prod == mult_res)

    ovf_exp = BitVec("ovf_exp", 8)
    ovf_prod = BitVec("ovf_product", 48)

    ovf_tuple = If(Extract(47, 47, ovf_prod) == 1, handle_ovf(pre_ovf_exp, prod),
                                                   mkOvfTuple(True, pre_ovf_exp, prod))

    constraint = And(constraint, get_ovf_tuple_cons(ovf_tuple))
    constraint = And(constraint, ovf_exp == get_ovf_tuple_exp(ovf_tuple))
    constraint = And(constraint, ovf_prod == get_ovf_tuple_prod(ovf_tuple))

    norm_exp = BitVec("norm_exp", 8)
    norm_prod = BitVec("norm_product", 48)

    norm_tuple = If(Extract(46, 46, ovf_prod) != 1, mult_norm(ovf_exp, ovf_prod), 
                                                    mkNormTuple(True, ovf_exp, ovf_prod))

    constraint = And(constraint, get_norm_cons(norm_tuple))
    constraint = And(constraint, norm_exp == get_norm_exp(norm_tuple))
    constraint = And(constraint, norm_prod == get_norm_prod(norm_tuple))

    constraint = And(constraint, out_exp == norm_exp)
    constraint = And(constraint, out_mant == Concat(BitVecVal(0, 1), Extract(46, 23, norm_prod)))
    constraint = And(constraint, out_mant_final == Extract(22, 0, out_mant))

    return out, constraint



def norm_sub_shift(in_exp, in_mant, num_lead_zeros):
    constraint = True

    norm_sub_exp = BitVec('norm_sub_exp', 8)
    norm_sub_prod = BitVec('norm_sub_mant', 48)
    lead_zeros_check = Int('lead_zeros_check')

    lead_zeros_prod_width = BitVec('lead_zeros_mant_width', 48)
    lead_zeros_exp_width = BitVec('lead_zeros_exp_width', 8)

    constraint = And(constraint, (lead_zeros_prod_width == BitVecVal(num_lead_zeros, 48)))
    constraint = And(constraint, (lead_zeros_exp_width == BitVecVal(num_lead_zeros, 8)))

    # constrain inputs to only numbers that do not require rounding
    # dude did not put a rounder into his FPU so FPU is guaranteed failing on inputs that need to be rounded
    # constraint = And(constraint, If(num_lead_zeros < 23, Extract((in_mant.size() - num_lead_zeros - 1), max((in_mant.size() - num_lead_zeros - 1 - 2), 0), in_mant) < BitVecVal(0b100, 3), True))
    
    constraint = And(constraint, norm_sub_prod == (in_mant << lead_zeros_prod_width))
    constraint = And(constraint, norm_sub_exp == (in_exp - lead_zeros_exp_width))

    ret_tuple = mkNormTuple(constraint, norm_sub_exp, norm_sub_prod)

    return ret_tuple



def mult_norm(in_exp, in_prod):

    norm_exp = BitVec("norm_exp", 8)
    norm_prod = BitVec("norm_prod", 48)

    # will become all 1's if we hit a case not explicitly defined
    # best I can come up with to mimic X's in systemVerilog
    norm_tuple = If(Extract(46, 41, in_prod) == BitVecVal(0b000001, 6), norm_sub_shift(in_exp, in_prod, 5), 
                    If(Extract(46, 42, in_prod) == BitVecVal(0b00001, 5), norm_sub_shift(in_exp, in_prod, 4), 
                       If(Extract(46, 43, in_prod) == BitVecVal(0b0001, 4), norm_sub_shift(in_exp, in_prod, 3), 
                          If(Extract(46, 44, in_prod) == BitVecVal(0b0001, 3), norm_sub_shift(in_exp, in_prod, 2), 
                             If(Extract(46, 45, in_prod) == BitVecVal(0b001, 2), norm_sub_shift(in_exp, in_prod, 1), 
                               mkNormTuple(True, BitVecVal(-1, 8), BitVecVal(-1, 48)))))))
    
    return norm_tuple



def bitwise_mult(a, b):

    constraint = True

    assert(a.size() == b.size())

    result = BitVec("result", 48)

    a_extend = BitVec("a_extend", 48)
    b_extend = BitVec("b_extend", 48)

    constraint = And(constraint, a_extend == Concat(BitVecVal(0, 48-a.size()), a))
    constraint = And(constraint, b_extend == Concat(BitVecVal(0, 48-b.size()), b))

    constraint = And(constraint, result == a_extend * b_extend)

    return result, constraint


if __name__ == "__main__":

    # a = BitVec('a', 24)
    # b = BitVec('b', 24)

    # constraint, out = bitwise_mult(a, b)

    # a_z = BitVec('a_z', 48)
    # b_z = BitVec('b_z', 48)
    # res_z = BitVec('res_z', 48)

    # solver = Solver()

    
    # solver.add(constraint)
    # solver.add(Extract(47, 24, a_z) == BitVecVal(0, 24))
    # solver.add(Extract(47, 24, b_z) == BitVecVal(0, 24))
    # solver.add(Extract(23, 0, a_z) == a)
    # solver.add(Extract(23, 0, b_z) == b)
    # solver.add(res_z == a_z * b_z)
    # solver.add(out != res_z)
    # if solver.check() == sat:
    #     print("Solution: ", solver.model())
    # else:
    #     print("No solution found")
   
    ###

    val_constraint = True
    a_float = FP('a_float', Float32())
    b_float = FP('b_float', Float32())

    a = BitVec('a', 32)
    b = BitVec('b', 32)

    
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

    
    dut_out, dut_constraint = fp_multiplier(a, b)

    solver = Solver()

    

    converted_out = fpToFP(dut_out, Float32())
    actual_val = FP('actual_val', Float32())
    solver.add(actual_val == (a_float * b_float))


    # uncomment for denorm bug output
    a_test = BitVecVal(0b00000001001001010100110011100110, 32)
    b_test = BitVecVal(0b00100111111100011011110001110110, 32)

    val_constraint = And(val_constraint, a == a_test)
    val_constraint = And(val_constraint, b == b_test)

    # comment out for denorm bug output, uncomment for rounding bug output
    # solver.add(fpIsNormal(actual_val) == True)
    a_test = BitVecVal(0b00000011111000101101001000101101, 32)
    b_test = BitVecVal(0b00111100111000110111010011010100, 32)

    val_constraint = And(val_constraint, a == a_test)
    val_constraint = And(val_constraint, b == b_test)

    solver.add(val_constraint)
    solver.add(dut_constraint)
    solver.add(converted_out != actual_val)
    if solver.check() == sat:
        print("Solution: ", solver.model())
    else:
        print("No solution found")
