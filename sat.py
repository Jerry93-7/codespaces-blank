from z3 import *
from BitVector import BitVector


def main():
    

    a = BitVec('a', 23)
    b = BitVec('b', 23)

    return subtractor(a, b)
    # return adder(a, b)
    
    print('testing commit')
 
def fp_adder_exp_AgeqB(a_sign, b_sign, out_sign, a_exp, b_exp, out_exp, a_mant, b_mant, out_mant):
    constraint = True

    exp_diff = BitVec('exp_diff', 8)

    tmp_mant = BitVec('exp_diff', 24)

    constraint = And(constraint, out_exp == a_exp)
    constraint = And(constraint, out_sign == a_sign)

    exp_diff_out, exp_diff_cons = subtractor(a_exp, b_exp)
    constraint = And(constraint, exp_diff == exp_diff_out)
    constraint = And(constraint, exp_diff_cons)

    constraint = And(constraint, tmp_mant == b_mant >> exp_diff)

    tmp_mant_low = Extract(23, 0, tmp_mant)
    mant_res, mant_res_cons, cout = If(a_sign == b_sign, adder(a_mant, tmp_mant_low), subtractor(a_mant, tmp_mant_low))
    constraint = And(constraint, Extract(23, 0, out_mant) == mant_res)
    constraint = And(constraint, Extract(24, 24, out_mant) == cout)
    constraint = And(constraint, mant_res_cons)

    return constraint, out_mant, out_exp, out_sign
    


def fp_adder_exp_BgeqA(a_sign, b_sign, out_sign, a_exp, b_exp, out_exp, a_mant, b_mant, out_mant):
    constraint = True

    exp_diff = BitVec('exp_diff', 8)

    tmp_mant = BitVec('exp_diff', 24)

    constraint = And(constraint, out_exp == b_exp)
    constraint = And(constraint, out_sign == b_sign)

    exp_diff_out, exp_diff_cons = subtractor(b_exp, a_exp)
    constraint = And(constraint, exp_diff == exp_diff_out)
    constraint = And(constraint, exp_diff_cons)

    constraint = And(constraint, tmp_mant == b_mant >> exp_diff)

    tmp_mant_low = Extract(23, 0, tmp_mant)
    mant_res, mant_res_cons, cout = If(a_sign == b_sign, adder(b_mant, tmp_mant_low), subtractor(b_mant, tmp_mant_low))
    constraint = And(constraint, Extract(23, 0, out_mant) == mant_res)
    constraint = And(constraint, Extract(24, 24, out_mant) == cout)
    constraint = And(constraint, mant_res_cons)

    return constraint, out_mant, out_exp, out_sign



def fp_adder_exp_eq_s_eq(a_sign, o_sign, a_mant, b_mant, out_mant):

    constraint = True

    add_out, add_cons, _ = adder(a_mant, b_mant)

    out_mant_low = Extract(23, 0, out_mant)

    constraint = And(constraint, add_cons)
    constraint = And(constraint, out_mant_low == add_out)
    constraint = And(constraint, o_sign == a_sign)

    out_mant_msb = Extract(24, 24, out_mant)
    constraint = And(constraint, out_mant_msb == 1)

    return constraint

def fp_adder_exp_eq_s_AgeqB(a_sign, o_sign, a_mant, b_mant, out_mant):

    constraint = True

    out_mant_low = Extract(22, 0, out_mant)

    sub_out, sub_cons, _ = subtractor(a_mant, b_mant)
    constraint = And(constraint, sub_cons)
    constraint = And(constraint, out_mant_low == sub_out)

    constraint = And(constraint, o_sign == a_sign)

    return constraint


def fp_adder_exp_eq_s_BgeqA(b_sign, o_sign, a_mant, b_mant, out_mant):

    constraint = True

    out_mant_low = Extract(22, 0, out_mant)

    sub_out, sub_cons, _ = subtractor(b_mant, a_mant)
    constraint = And(constraint, sub_cons)
    constraint = And(constraint, out_mant_low == sub_out)

    constraint = And(constraint, o_sign == b_sign)

    return constraint




def fp_adder(a, b):

    assert(a.size() == b.size())

    constraint = True

    out = BitVec('out', 32)

    out_mant = BitVec('out', 25)

    out_sign = Extract(31, 31, out)
    out_exp = Extract(30, 23, out)
    out_mant_final = Extract(22, 0, out_mant)

    a_sign = Extract(31, 31, a)
    a_exp = Extract(30, 23, a)
    a_mant = Extract(22, 0, a)

    b_sign = Extract(31, 31, b)
    b_exp = Extract(30, 23, b)
    b_mant = Extract(22, 0, b)

    hidden_bit = BitVec('hidden_bit', 1)

    constraint = And(constraint, (hidden_bit == 1))
    a_mant_full = Concat(hidden_bit, a_mant)
    b_mant_full = Concat(hidden_bit, b_mant)

    non_norm_out, non_norm_constraint = If(a_exp == b_exp, 
                            If(a_sign == b_sign, fp_adder_exp_eq_s_eq(a_sign, out_sign, a_mant_full, b_mant_full, out_mant),  
                                                If(a_mant_full > b_mant_full, fp_adder_exp_eq_s_AgeqB(a_sign, out_sign, a_mant_full, b_mant_full, out_mant), 
                                                                              fp_adder_exp_eq_s_BgeqA(a_sign, out_sign, a_mant_full, b_mant_full, out_mant))), 
                                                                                                    If(a_exp > b_exp, fp_adder_exp_AgeqB(a_sign, b_sign, out_sign, a_exp, b_exp, out_exp, a_mant, b_mant, out_mant), 
                                                                                                                      fp_adder_exp_BgeqA(a_sign, b_sign, out_sign, a_exp, b_exp, out_exp, a_mant, b_mant, out_mant)))
                                                                            # exponents not same function in remaining case
    



# out = a - b
def subtractor(a, b):

    constraint = True

    assert(a.size() == b.size())
    out = BitVec('out', a.size())

    throwaway = BitVecVal(0, 1)

    borrow_in = BitVec('carry_out', a.size() + 1)

    constraint = And(constraint, (Extract(0, 0, borrow_in) == 0))

    for i in range(a.size()):
        out_bit = Extract(i, i, out)
        a_bit = Extract(i, i, a)
        b_bit = Extract(i, i, b)
        borrow_in_curr = Extract(i, i, borrow_in)
        borrow_in_next = Extract(i+1, i+1, borrow_in)

        
        constraint = And(constraint, (out_bit == a_bit ^ b_bit ^ borrow_in_curr))
        constraint = And(constraint, (borrow_in_next == (~(a_bit ^ b_bit)) & borrow_in_curr | ((~a_bit) & b_bit)))

    return out, constraint, throwaway


def adder(a, b):

    constraint = True

    assert(a.size() == b.size())
    out = BitVec('out', a.size())

    carry_out = BitVec('carry_out', a.size()+1)

    constraint = And(constraint, (Extract(0, 0, carry_out) == 0))

    for i in range(a.size()):
        out_bit = Extract(i, i, out)
        a_bit = Extract(i, i, a)
        b_bit = Extract(i, i, b)
        carry_out_bit_curr = Extract(i, i, carry_out)
        carry_out_bit_next = Extract(i+1, i+1, carry_out)

        
        constraint = And(constraint, (out_bit == a_bit ^ b_bit ^ carry_out_bit_curr))
        constraint = And(constraint, (carry_out_bit_next == (a_bit & b_bit) | ((a_bit ^ b_bit) & carry_out_bit_curr)))

    return out, constraint, Extract(a.size()+1, a.size()+1, carry_out)

if __name__ == "__main__":

    # a = FP('a', Float32())
    # b = FP('b', Float32())
    a = BitVec('a', 23)
    b = BitVec('b', 23)

    out, constraint = main()

    solver = Solver()
    solver.add(constraint)
    solver.add(out != (a - b))
    if solver.check() == sat:
        print("Solution: ", solver.model())
    else:
        print("No solution found")



