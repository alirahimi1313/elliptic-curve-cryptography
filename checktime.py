__author__ = 'mahdi'

import random
import time

import ECC


def readtime(s, func):
    f = open(s)
    lines = f.readlines()
    start = time.time()
    for line in lines:
        line = line.strip()
        q = long(line.split(' ')[0])
        n = long(line.split(' ')[1])
        func(n, q)
    end = time.time()
    f.close()
    print end - start


def genfilelowbit(s, max, N=1000):
    f = open(s, 'w+')
    for i in range(N):
        p = random.randint(10, max)
        n = random.randint(1, p)
        f.write('{0} {1}\n'.format(p, n))
    f.close()


def genfile(s, N=1000):
    p = 262056257502347001737855788823938224577L
    f = open(s, 'w+')
    for i in range(N):
        n = random.getrandbits(127)
        f.write('{0} {1}\n'.format(p, n))
    f.close()


if __name__ == "__main__":
    # genfilelowbit('data_1e24.txt', 1e24)
    # for i in range(6, 25, 3):
    #     s = 'data_1e' + str(i) + '.txt'
    #     readtime(s, ECC.inv)

    # genfile('data.txt', 100000)

    # readtime('data.txt', ECC.inv)
    # readtime('data.txt', ECC.inv2)

    readtime('data.txt', ECC.sqrt)
