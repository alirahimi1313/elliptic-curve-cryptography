# basics of elliptic curve cryptography implementation on python
import operator
import collections
import random
import math
import os
#import psutil

import sys

__author__ = 'mahdi'


def inv(n, q):
    """div on pn modulo a/b mod q as a * inv(b, q) mod q
    >>> assert n * inv(n, q) % q == 1
    """
    # n*inv % q = 1 => n*inv = q*m + 1 => n*inv + q*-m = 1
    # => egcd(n, q) = (inv, -m, 1) => inv = egcd(n, q)[0] (mod q)
    e = egcd(n, q)
    assert e[2] == 1
    return e[0] % q
    # [ref] naive implementation
    # for i in range(q):
    #    if (n * i) % q == 1:
    #        return i
    #    pass
    # assert false, "unreached"
    # pass


def egcd(a, b):
    """extended gcd
    returns: (s, t, gcd) as a*s + b*t == gcd
    >>> s, t, gcd = egcd(a, b)
    >>> assert a % gcd == 0 and b % gcd == 0
    >>> assert a * s + b * t == gcd
    """
    s0, s1, t0, t1 = 1, 0, 0, 1
    while b > 0:
        q, r = divmod(a, b)
        a, b = b, r
        s0, s1, t0, t1 = s1, s0 - q * s1, t1, t0 - q * t1
        pass
    return s0, t0, a


def inv2(n, q):
    """another pn invmod: from euler totient function
    - n ** (q - 1) % q = 1 => n ** (q - 2) % q = n ** -1 % q
    """
    assert q > 2
    s, p2, p = 1, n, q - 2
    while p > 0:
        if p & 1 == 1: s = s * p2 % q
        p, p2 = p >> 1, pow(p2, 2, q)
        pass
    return s


def sqrt2(n, q):
    """sqrt on pn modulo: returns two numbers or exception if not exist
    >>> assert (sqrt(n, q)[0] ** 2) % q == n
    >>> assert (sqrt(n, q)[1] ** 2) % q == n
    """
    assert n < q
    for i in range(1, q):
        if pow(i, 2, q) == n:
            return (i, q - i)
        pass
    raise Exception("not found")


def sqrt(n, q):
    """sqrtmod for bigint
    - algorithm 3.34 of http://www.cacr.math.uwaterloo.ca/hac/about/chap3.pdf
    """
    import random
    # b: some non-quadratic-residue
    b = 0
    while b == 0 or jacobi(b, q) != -1:
        b = random.randint(1, q - 1)
        pass
    # q = t * 2^s + 1, t is odd
    t, s = q - 1, 0
    while t & 1 == 0:
        t, s = t >> 1, s + 1
        pass
    assert q == t * pow(2, s) + 1 and t % 2 == 1
    ni = inv(n, q)
    c = pow(b, t, q)
    r = pow(n, (t + 1) // 2, q)
    for i in range(1, s):
        d = pow(pow(r, 2, q) * ni % q, pow(2, s - i - 1, q), q)
        if d == q - 1: r = r * c % q
        c = pow(c, 2, q)
        pass
    return (r, q - r)


def jacobi2(a, q):
    """jacobi symbol: judge existing sqrtmod (1: exist, -1: not exist)
    - j(a*b,q) = j(a,q)*j(b,q)
    - j(a*q+b, q) = j(b, q)
    - j(a, 1) = 1
    - j(0, q) = 0
    - j(2, q) = -1 ** (q^2 - 1)/8
    - j(p, q) = -1 ^ {(p - 1)/2 * (q - 1)/2} * j(q, p)
    """
    if q == 1: return 1
    if a == 0: return 0
    if a % 2 == 0: return (-1) ** ((q * q - 1) // 8) * jacobi2(a // 2, q)
    return (-1) ** ((a - 1) // 2 * (q - 1) // 2) * jacobi2(q % a, a)


def jacobi(a, q):
    """quick jacobi symbol
    - algorithm 2.149 of http://www.cacr.math.uwaterloo.ca/hac/about/chap2.pdf
    """
    if a == 0: return 0
    if a == 1: return 1
    a1, e = a, 0
    while a1 & 1 == 0:
        a1, e = a1 >> 1, e + 1
        pass
    m8 = q % 8
    s = -1 if m8 == 3 or m8 == 5 else 1  # m8 = 0,2,4,6 and 1,7
    if q % 4 == 3 and a1 % 4 == 3: s = -s
    return s if a1 == 1 else s * jacobi(q % a1, a1)


coord = collections.namedtuple("coord", ["x", "y"])


class EllipticCurve(object):
    """system of elliptic curve"""

    def __init__(self, a, b, q):
        """elliptic curve as: (y**2 = x**3 + a * x + b) mod q
        - a, b: params of curve formula
        - q: prime number
        """
        assert 0 < a and a < q and 0 < b and b < q and q > 2
        assert (4 * (a ** 3) + 27 * (b ** 2)) % q != 0
        self.a = a
        self.b = b
        self.q = q
        # just as unique zero value representation for "add": (not on curve)
        self.zero = coord(0, 0)
        pass

    def is_valid(self, p):
        if p == self.zero: return True
        l = (p.y ** 2) % self.q
        r = ((p.x ** 3) + self.a * p.x + self.b) % self.q
        return l == r

    def at(self, x):
        """find points on curve at x
        - x: int < q
        - returns: ((x, y), (x,-y)) or not found exception
        >>> a, ma = ec.at(x)
        >>> assert a.x == ma.x and a.x == x
        >>> assert a.x == ma.x and a.x == x
        >>> assert ec.neg(a) == ma
        >>> assert ec.is_valid(a) and ec.is_valid(ma)
        """
        assert x < self.q
        ysq = (x ** 3 + self.a * x + self.b) % self.q
        y, my = sqrt(ysq, self.q)
        return coord(x, y), coord(x, my)

    def neg(self, p):
        """negate p
        >>> assert ec.is_valid(ec.neg(p))
        """
        return coord(p.x, -p.y % self.q)

    def add(self, p1, p2):
        """<add> of elliptic curve: negate of 3rd cross point of (p1,p2) line
        >>> d = ec.add(a, b)
        >>> assert ec.is_valid(d)
        >>> assert ec.add(d, ec.neg(b)) == a
        >>> assert ec.add(a, ec.neg(a)) == ec.zero
        >>> assert ec.add(a, b) == ec.add(b, a)
        >>> assert ec.add(a, ec.add(b, c)) == ec.add(ec.add(a, b), c)
        """
        if p1 == self.zero: return p2
        if p2 == self.zero: return p1
        if p1.x == p2.x and (p1.y != p2.y or p1.y == 0):
            # p1 + -p1 == 0
            return self.zero
        if p1.x == p2.x:
            # p1 + p1: use tangent line of p1 as (p1,p1) line
            l = (3 * p1.x * p1.x + self.a) * inv(2 * p1.y, self.q) % self.q
            pass
        else:
            l = (p2.y - p1.y) * inv(p2.x - p1.x, self.q) % self.q
            pass
        x = (l * l - p1.x - p2.x) % self.q
        y = (l * (p1.x - x) - p1.y) % self.q
        return coord(x, y)

    def mul(self, p, n):
        """n times <mul> of elliptic curve
        >>> m = ec.mul(p, n)
        >>> assert ec.is_valid(m)
        >>> assert ec.mul(p, 0) == ec.zero
        """
        r = self.zero
        m2 = p
        # o(log2(n)) add
        while 0 < n:
            if n & 1 == 1:
                r = self.add(r, m2)
                pass
            n, m2 = n >> 1, self.add(m2, m2)
            pass
        # [ref] o(n) add
        # for i in range(n):
        #    r = self.add(r, p)
        #    pass
        return r

    def order(self, g):
        """order of point g
        >>> o = ec.order(g)
        >>> assert ec.is_valid(g) and ec.mul(g, o) == ec.zero
        >>> assert o <= ec.q
        """
        # return self.q

        assert self.is_valid(g) and g != self.zero
        for i in range(1, self.q + 1):
            if self.mul(g, i) == self.zero:
                return i
            pass
        raise Exception("invalid order")

    pass


class elgamal(object):
    """elgamal encryption
    pub key encryption as replacing (mulmod, powmod) to (ec.add, ec.mul)
    - ec: elliptic curve
    - g: (random) a point on ec
    """

    def __init__(self, ec, g):
        assert ec.is_valid(g)
        self.ec = ec
        self.g = g
        # self.n = ec.order(g)
        pass

    def gen(self, priv):
        """generate pub key
        - priv: priv key as (random) int < ec.q
        - returns: pub key as points on ec
        """
        return self.ec.mul(self.g, priv)

    def enc(self, plain, pub, r):
        """encrypt
        - plain: data as a point on ec
        - pub: pub key as points on ec
        - r: randam int < ec.q
        - returns: (cipher1, ciper2) as points on ec
        """
        assert self.ec.is_valid(plain)
        assert self.ec.is_valid(pub)
        return (self.ec.mul(self.g, r), self.ec.add(plain, self.ec.mul(pub, r)))

    def dec(self, cipher, priv):
        """decrypt
        - chiper: (chiper1, chiper2) as points on ec
        - priv: private key as int < ec.q
        - returns: plain as a point on ec
        """
        c1, c2 = cipher
        assert self.ec.is_valid(c1) and ec.is_valid(c2)
        return self.ec.add(c2, self.ec.neg(self.ec.mul(c1, priv)))

    pass


class diffiehellman(object):
    """elliptic curve diffie hellman (key agreement)
    - ec: elliptic curve
    - g: a point on ec
    """

    def __init__(self, ec, g):
        self.ec = ec
        self.g = g
        self.n = ec.order(g)
        pass

    def gen(self, priv):
        """generate pub key"""
        # assert 0 < priv and priv < self.n
        return self.ec.mul(self.g, priv)

    def secret(self, priv, pub):
        """calc shared secret key for the pair
        - priv: my private key as int
        - pub: partner pub key as a point on ec
        - returns: shared secret as a point on ec
        """
        assert self.ec.is_valid(pub)
        assert self.ec.mul(pub, self.n) == self.ec.zero
        return self.ec.mul(pub, priv)

    pass


class DSA(object):
    """ecdsa
    - ec: elliptic curve
    - g: a point on ec
    """

    def __init__(self, ec, g):
        self.ec = ec
        self.g = g
        self.n = ec.order(g)
        pass

    def gen(self, priv):
        """generate pub key"""
        assert 0 < priv and priv < self.n
        return self.ec.mul(self.g, priv)

    def sign(self, hashval, priv, r):
        """generate signature
        - hashval: hash value of message as int
        - priv: priv key as int
        - r: random int
        - returns: signature as (int, int)
        """
        assert 0 < r and r < self.n
        m = self.ec.mul(self.g, r)
        return (m.x, inv(r, self.n) * (hashval + m.x * priv) % self.n)

    def validate(self, hashval, sig, pub):
        """validate signature
        - hashval: hash value of message as int
        - sig: signature as (int, int)
        - pub: pub key as a point on ec
        """
        assert self.ec.is_valid(pub)
        assert self.ec.mul(pub, self.n) == self.ec.zero
        w = inv(sig[1], self.n)
        u1, u2 = hashval * w % self.n, sig[0] * w % self.n
        p = self.ec.add(self.ec.mul(self.g, u1), self.ec.mul(pub, u2))
        return p.x % self.n == sig[0]

    pass


def bsgs_ec(ec, h, p, n):
    m = int(math.ceil(math.sqrt(n)))
    tjp = []
    for j in range(m):
        tjp.append(ec.mul(p, j))
    r = ec.mul(ec.neg(p), m)
    y = h
    for i in range(m):
        if (tjp.count(y) > 0):
            # print i, m, tjp.index(y)
            return i * m + tjp.index(y)
        y = ec.add(y, r)
    return -1


# p = 131
# ec = ec(7, 18, p)
# g = ec.zero
# while g == ec.zero or not ec.is_valid(g):
#     g, _ = ec.at(66)#random.getrandbits(7))
# # print g, ec.order(g)
# eg = elgamal(ec, g)
# s = 67
# pub = eg.gen(s)
# r = random.getrandbits(4)
# c = eg.enc(ec.mul(g, 54), pub, r)
# d = eg.dec(c, s)
# for i in range(p):
#     if(ec.mul(g, i) == d):
#         print i, 1
# print bsgs_ec(ec, d, g, p)


k = 80  # 80, 160, 240
m = sys.argv[1] if(len(sys.argv) > 1) else 2
lres = (0, [0]*m)
file = open('log.txt', 'w+')


def refrandom(ec):
    g = ec.zero
    while g == ec.zero or not ec.is_valid(g):
        g, _ = ec.at(random.getrandbits(2*k))
    # assert ec.order(g) <= ec.q

    # elgamal enc/dec usage
    eg = elgamal(ec, g)
    # mapping value to ec point
    # "masking": value k to point ec.mul(g, k)
    # ("imbedding" on proper n:use a point of x as 0 <= n*v <= x < n*(v+1) < q)
    # mapping = [ec.mul(g, i) for i in range(eg.n)]

    n = [100, 200, 500,
         # 1000, 2000, 5000,
         # 10000, 20000, 50000,
         # 100000       , 200000       , 500000       ,
         1000000#      , 2000000      , 5000000      ,
         # 10000000     , 20000000     , 50000000     ,
         # 100000000    , 200000000    , 500000000    ,
         # 1000000000   , 2000000000   , 5000000000   ,
         # 10000000000  , 20000000000  , 50000000000  ,
         # 100000000000 , 200000000000 , 500000000000 ,
         # 1000000000000,
         ]

    '''
    # code for linear dec
    # for n in n:
    n = n[-1]
    k = 0
    if 1:
        plain = ec.zero
        import time
        start = time.time()
        for i in range(n):
            plain = ec.add(plain, g)
            # plain = ec.mul(g, i)
            if(n[k] == i):
                k+=1
                end = time.time()
                print i, end-start
        end = time.time()
        print n, end-start
    '''

    global file

    for n in n:
        plain = ec.zero
        import time
        start = time.time()
        bsgs_ec(ec, ec.mul(g, n - 1), g, n)
        end = time.time()
        print (n, end - start)
        file.write(str((n, end - start))+'\n')
        file.flush()

    priv = random.getrandbits(160)
    pub = eg.gen(priv)

    cipher = eg.enc(plain, pub, random.getrandbits(160))
    decoded = eg.dec(cipher, priv)
    # print decoded
    assert decoded == plain
    assert cipher != pub

    return


def f2(set, gs, ec):
    assert len(set) == len(gs), 'vector sizes must match'
    out = ec.zero
    for k in range(len(set)):
        out = ec.add(out, ec.mul(gs[k], set[k]))
    return out


def f(set, gs, ec):
    global lres
    assert len(set) == len(gs), 'vector sizes must match'
    out = ec.zero
    diff = map(operator.sub, set, lres[1])
    if(sum(map(operator.pow, diff, [2]*len(diff))) == 2):
        out = lres[0]
        for k in range(len(diff)):
            if(diff[k] < 0):
                out = ec.add(out, ec.neg(gs[k]))
            elif(diff[k] > 0):
                out = ec.add(out, gs[k])
    else:
        for k in range(len(set)):
            out = ec.add(out, ec.mul(gs[k], set[k]))
    lres = (out, list(set))
    return out


def check(n, ec, gs=[], set=[], target=None):
    global file
    k = gs.__len__()
    # if set == [10, 0, 0]:
    #     print set
    if set.__len__() < k - 1:
        for i in range(n - sum(set) + 1):
            set.append(i)
            if (check(n, ec, gs, set, target)):
                return True
            set.pop()
            # return False
    else:
        if (sum(map(operator.mod, set, [k*10]*len(set))) == 0):
            print(set)
            file.write(str(set)+'\n')
            file.flush()
        set.append(n - sum(set))
        res = f(set, gs, ec)
        if (target == res):
            print(set)
            file.write(str(set)+'\n')
            file.flush()
            return True
        set.pop()
        return False


def check2(n, k):#gs=[], set=[], res=None):
    # if set == [10, 0, 0]:
    #     print set
    # x1 + ... + xk = n

    s = [0] * k
    s[0] = n
    i = 0
    inc = -1

    while True:
        if(s[0] + inc <= n and s[0] + inc >= 0):
            s[0] += inc

            i = 1
            while i < n and (not (s[i] - inc <= n and s[i] - inc >= 0)):
                i += 1
            else:
                s[i] -= inc
                print(s)
                continue
            break
        else:
            inc = -inc
            continue


def voting(m, ec):
    global file
    gs = []
    while gs.__len__() < m:
        g = ec.zero
        while g == ec.zero or not ec.is_valid(g):
            g, _ = ec.at(random.getrandbits(2*k))
        gs.append(g)

    n = [100, 200, 500,
         1000, 2000, 5000,
         10000, 20000, 50000,
         # 100000       , 200000       , 500000       ,
         # 1000000      , 2000000      , 5000000      ,
         # 10000000     , 20000000     , 50000000     ,
         # 100000000    , 200000000    , 500000000    ,
         # 1000000000   , 2000000000   , 5000000000   ,
         # 10000000000  , 20000000000  , 50000000000  ,
         # 100000000000 , 200000000000 , 500000000000 ,
         # 1000000000000,
         ]
    res = ec.mul(gs[0], n[0])
    import time
    start = time.time()

    r = check(n[0], ec, gs, [], res)
    print(r)
    file.write(str(r)+'\n')
    file.flush()



    end = time.time()
    print (m, n[0], end - start)
    file.write(str((m, n[0], end - start))+'\n')
    file.flush()


    return


def other_check():
    # shared elliptic curve system of examples
    ec = EllipticCurve(1268133167195989090596625406312984755854486256116,
                       386736940269827655214118852806596527602892573734,
                       1461501637330902918203684832716283019655932542983)
    g, _ = ec.at(random.getrandbits(160))
    assert ec.order(g) <= ec.q

    # ecdh usage
    dh = diffiehellman(ec, g)

    apriv = 11
    apub = dh.gen(apriv)

    bpriv = 3
    bpub = dh.gen(bpriv)

    cpriv = 7
    cpub = dh.gen(cpriv)
    # same secret on each pair
    assert dh.secret(apriv, bpub) == dh.secret(bpriv, apub)
    assert dh.secret(apriv, cpub) == dh.secret(cpriv, apub)
    assert dh.secret(bpriv, cpub) == dh.secret(cpriv, bpub)

    # not same secret on other pair
    assert dh.secret(apriv, cpub) != dh.secret(apriv, bpub)
    assert dh.secret(bpriv, apub) != dh.secret(bpriv, cpub)
    assert dh.secret(cpriv, bpub) != dh.secret(cpriv, apub)

    # ecdsa usage
    dsa = DSA(ec, g)

    priv = 11
    pub = ec.gen(priv)
    hashval = 128
    r = 7

    sig = dsa.sign(hashval, priv, r)
    assert dsa.validate(hashval, sig, pub)
    pass


# check(6, [1] * 3)

if __name__ == "__main__":
    # shared elliptic curve system of examples
    if k < 80:
        ec = EllipticCurve(5,
                           7,
                           223)
    elif k == 80:
        ec = EllipticCurve(1268133167195989090596625406312984755854486256116,
                           386736940269827655214118852806596527602892573734,
                           1461501637330902918203684832716283019655932542983)
    elif k == 160:
        ec = EllipticCurve(
            2088105959680623325842477250435045284830027862785870211433492825096738057013555851670055268682213,
            1163755670441028554302599764553789716846705580467529854789623514071878399983353288619261210338191,
            5339967589802275205987554265423880286506761306039270277656609164265354514010464991959371747702617)
    elif k == 240:
        ec = EllipticCurve(
            2707069958412506902602824447813694027990688183956223888320767933486020623060222427867360955451044640503732397723488780961683652364955407331149336,
            4536433587307211432323192274338329543592280212783596492035047326660663646635350354568929622029507484145388525397790533006611631792360854156270441,
            9950573504132225237528841169965717599573656580696044268676583193632704892755795210303651532931596765152853320844768094929978936522271668818569113)

    # for m in range(5, 6):
    if(1):

        if (m == 2):
            refrandom(ec)
        else:
            lres = (0, [0]*m)
            voting(m, ec)

    #print(psutil.virtual_memory())
    # process = psutil.process(os.getpid())
    # print(process.memory_info())

if __name__ == "__main__2":
    # shared elliptic curve system of examples
    ec = EllipticCurve(1268133167195989090596625406312984755854486256116,
                       386736940269827655214118852806596527602892573734,
                       1461501637330902918203684832716283019655932542983)

    check2(5, 3)

    #print(psutil.virtual_memory())
    # process = psutil.process(os.getpid())
    # print(process.memory_info())
