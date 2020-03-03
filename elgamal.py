import random
import math

__author__ = 'mahdi'


def inv(n, q):
    """div on PN modulo a/b mod q as a * inv(b, q) mod q
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
    # assert False, "unreached"
    # pass


def egcd(a, b):
    """extended GCD
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


def power(n, p, q):
    r = 1
    m = n
    # O(log2(n)) mul
    while 0 < p:
        if p & 1 == 1:
            r = r * m % q
            pass
        p, m = p >> 1, m * m % q
        pass
    return r


class ElGamal(object):
    """ElGamal Encryption
    pub key encryption as replacing (mulmod, powmod) to (ec.add, ec.mul)
    - p: prime number
    - g: (random) a point on ec
    """

    def __init__(self, p, g):
        self.p = p
        self.g = g % p
        self.n = p - 1 #self.order(g)
        pass

    def gen(self, priv):
        """generate pub key
        - priv: priv key as (random) int < ec.q
        - returns: pub key as points on ec
        """
        self.__priv = priv
        self.pub = power(self.g, priv, self.p)
        return self.pub

    def enc(self, plain, pub, r):
        """encrypt
        - plain: data as a point on ec
        - pub: pub key as points on ec
        - r: randam int < ec.q
        - returns: (cipher1, ciper2) as points on ec
        """
        return (power(self.g, r, self.p), power(self.g, plain, self.p) * power(pub, r, self.p) % self.p)

    def dec(self, cipher, priv):
        """decrypt
        - chiper: (chiper1, chiper2) as points on ec
        - priv: private key as int < ec.q
        - returns: plain as a point on ec
        """
        c1, c2 = cipher
        return power(inv(c1, self.p), priv, self.p) * c2 % self.p

    pass


def bsgs(h, g, n, q):
    m = int(math.ceil(math.sqrt(n)))
    tgj = []
    for j in range(m):
        tgj.append(power(g, j, q))
    r = power(inv(g, q), m, q)
    y = h
    for i in range(m):
        if(tgj.count(y) > 0):
            return i*m + tgj.index(y)
        y = y*r % q
    return -1



# p = 17
# g = 5
# el = ElGamal(p, g)
# s = 13
# pub = el.gen(s)
# r = random.getrandbits(4)
# c = el.enc(7, pub, 4)
# d = el.dec(c, s)
# for i in range(p):
#     if(power(g, i, p) == d):
#         print i
# print bsgs(d, g, p, p)

if __name__ == "__main__":
    # shared elliptic curve system of examples

    el = ElGamal(171578104362074095910441789677735234962674526519244199389899886988970706066807887945978534189871042766708191122222066053564256474542247781766390916256855763922711820807938460387250117442154224915848774792412439798804686071433922354235169407590952215291874454956068820025755088098501551831607911311781089167459L,
                 77106717981373534049609423898450068698536158473427980808306145849112225828190841255769681689721214731272454515552536939017789846419830541651719914734215709001474072975558189065597410910848895556587792004518647655138291986827353266580737818260745885307371115673586130825728981034904911723478701333945384939409L)

    N = [100          , 200          , 500          ,
         1000         , 2000         , 5000         ,
         10000        , 20000        , 50000        ,
         100000       , 200000       , 500000       ,
         1000000      , 2000000      , 5000000      ,
         10000000     , 20000000     , 50000000     ,
         100000000    , 200000000    , 500000000    ,
         # 1000000000   , 2000000000   , 5000000000   ,
         # 10000000000  , 20000000000  , 50000000000  ,
         # 100000000000 , 200000000000 , 500000000000 ,
         # 1000000000000,
         ]

    '''
    # code for linear dec
    # for n in N:
    n = N[-1]
    k = 0
    if 1:
        plain = 1
        import time
        start = time.time()
        for i in range(n):
            plain = plain * el.g % el.p
            # plain = power(el.g, i, el.p)
            if(N[k] == i):
                k += 1
                end = time.time()
                print i, end-start
        end = time.time()
        print n, end-start
    '''

    for n in N:
        plain = 1
        import time
        start = time.time()
        bsgs(power(el.g, n - 1, el.p), el.g, n, el.p)
        end = time.time()
        print n, end-start



        # ElGamal enc/dec usage