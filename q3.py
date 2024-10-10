import prover as p
import compiler as c
import verifier as v
from utils import f_inner
import math

setup = c.Setup.from_file("powersOfTau28_hez_final_11.ptau")


def circuit(n, s_len, i_in):
    """
    General approach:
    1. Assign inputs as public witnesses
    2. Check that the input is in the range [0, n)
    3. For each ciphertext ct_j = (a_j, b_j), encrypt message p as b'_j <- <s, a_j> + p
    4. Create the selector vector for the index i and use it to select both b'_i and the actual b_i
    5. Constrain the b'_i = b_i, showing ciphertext ct_i is a valid encryption of message p under the secret key s
    (hence proving the prover knows a secret key s such that p is the decryption of ct_i under s)
    """
    eqs = []
    eqs.extend(gen_public_input_eqs(n, s_len))
    eqs.extend(check_i_in_range(n, i_in))
    for i in range(n):
        eqs.extend(gen_encrypt(i, s_len))
    eqs.extend(create_index_selector(n, i_in))
    eqs.extend(create_selector_mask_and_select(n, "claimedB"))
    eqs.extend(create_selector_mask_and_select(n, "b"))
    eqs.append("selclaimedB === selb")
    return eqs


def gen_input_assigments(i_in, ct_in, p_in, s_in):
    """
    Given the public inputs i, ct_0, ct_1, ..., ct_n, p, and the secret key s
    generate the witness assignments (handling assignment of vectors) and
    return a dictionary of all the input assignments.
    """
    assignments = {}
    public = []
    for i in range(len(ct_in)):
        for j in range(len(s_in)):
            assignments["a{}{}".format(i, j)] = ct_in[i][0][j]
            public.append(ct_in[i][0][j])
        assignments["b{}".format(i)] = ct_in[i][1]
        public.append(ct_in[i][1])

    for i in range(len(s_in)):
        assignments["s{}".format(i)] = s_in[i]
    assignments["i"] = i_in
    public.append(i_in)
    assignments["p"] = p_in
    public.append(p_in)
    return assignments, public


def gen_public_input_eqs(n, s_len):
    """
    Generate the public input declarations for the circuit
    """
    eqs = []
    for i in range(n):
        for j in range(s_len):
            eqs.append("a{}{}pub public".format(i, j))
            eqs.append("a{}{}pub <== a{}{}".format(i, j, i, j))
        eqs.append("b{}pub public".format(i))
        eqs.append("b{}pub <== b{}".format(i, i))
    eqs.append("ipub public")
    eqs.append("ipub <== i")
    eqs.append("ppub public")
    eqs.append("ppub <== p")
    eqs.sort(key=lambda x: "public" not in x)
    return eqs


def gen_encrypt(a, s_len):
    """
    Given an index `a`, constrains the encryption of `p` using the first part of
    ciphertext `ct_a` (b <- <s, a> + p), storing the result as `claimedB_a`.
    """
    eqs = []
    for i in range(s_len):
        eqs.append("a{}mul{} <== s{} * a{}{}".format(a, i, i, a, i))

    eqs.append("a{}add1 <== a{}mul0 + a{}mul1".format(a, a, a))
    for i in range(2, s_len):
        eqs.append(
            "a{}add{} <== {} + {}".format(
                a, i, "a{}add{}".format(a, i - 1), "a{}mul{}".format(a, i)
            )
        )

    eqs.append("claimedB{} <== {} + p".format(a, "a{}add{}".format(a, s_len - 1)))

    return eqs


def create_index_selector(n, i_val):
    """
    Given an index `i_val`, creates a vector of contraints that sets
    `sel{i}` to 1 if `i` is equal to `i_val`, and 0 otherwise.
    """
    eqs = []
    for i in range(n):
        """
        For each index `i` we compute the difference `i - i_val`, and
        then check if it is equal to 0. If it is, we set `sel{i}` to 1,
        otherwise we set it to 0. We do this by providing the inverse of the difference as a witness if it exists, 
        else 0, and then computing -inv * diff + 1. This quantity is 1 only if the diff is 0.
        This is inspired by 
        https://github.com/iden3/circomlib/blob/cff5ab6288b55ef23602221694a6a38a0239dcc0/circuits/comparators.circom#L24.
        The resulting vector has a 1 at the index `i_val` and 0 everywhere else.
        """

        eqs.append("sel{}first <== {} - i".format(i, i))
        diff = i - i_val
        inv = f_inner(1) / diff if diff != 0 else 0
        eqs.append("inv{} <== {}".format(i, inv))
        eqs.append("sel{}second <== sel{}first * inv{}".format(i, i, i))
        eqs.append("sel{} <== sel{}second * -1 + 1".format(i, i))
    return eqs


def create_selector_mask_and_select(n, x):
    """
    Given some variable x, which is a vector, select based on the global `i_val` variable 
    by taking the inner product of `sel` and `x` (causing all elements of `x` to be zeroed
    out except the value at index `i`).
    """
    eqs = []
    for i in range(n):
        eqs.append("sel{}{}mask <== sel{} * {}{}".format(x, i, i, x, i))
    eqs.append("selSum{}1 <== sel{}0mask + sel{}1mask".format(x, x, x))
    for i in range(2, n):
        eqs.append(
            "selSum{}{} <== selSum{}{} + sel{}{}mask".format(x, i, x, i - 1, x, i)
        )
    eqs.append("sel{} <== selSum{}{}".format(x, x, n - 1))
    return eqs


def check_i_in_range(n, i_in):
    """
    Given an index `i_in`, constrains the index to be in the range [0, n)
    by decomposing into log_2(n) bits, constraining each bit to be 0 or 1,
    and then constraining that when reconstructed, it is equal to `i_in`.
    """
    eqs = []
    bit_len = int(math.log(n, 2))
    i_in_bits = [int(b) for b in bin(i_in)[2:].zfill(bit_len)]
    i_in_bits.reverse()
    for i in range(bit_len):
        pow2 = 2**i
        eqs.append("pow2{} <== {}".format(i, pow2))
        eqs.append("ibit{} <== {}".format(i, i_in_bits[i]))
        eqs.append("ibit{} === ibit{} * ibit{}".format(i, i, i))
        eqs.append("imask{} <== pow2{} * ibit{}".format(i, i, i))

    eqs.append("isum1 <== imask0 + imask1")
    for i in range(2, bit_len):
        eqs.append("isum{} <== isum{} + imask{}".format(i, i - 1, i))

    eqs.append("i === isum{}".format(bit_len - 1))
    return eqs


S_LEN = 3
N = 8

ct_in = [
    ((3, 7, 11), 5),
    ((8, 2, 5), 19),
    ((5, 7, 2), 11),
    ((3, 1, 1), 8),
    ((2, 0, 10), 10),
    ((6, 12, 3), 5),
    ((5, 9, 3), 11),
    ((1, 0, 7), 5),
]
p_in = 6
s_in = (1, 0, 1)
i_in = 1
eqs = circuit(N, S_LEN, i_in)
vk = c.make_verification_key(setup, 256, eqs)
print("Generated verification key")
input_assignments, public = gen_input_assigments(i_in, ct_in, p_in, s_in)
assignments = c.fill_variable_assignments(eqs, input_assignments)
proof = p.prove_from_witness(setup, 256, eqs, assignments)
print("Generated proof")
assert v.verify_proof(setup, 256, vk, proof, public, optimized=True)
print("Verified proof")
