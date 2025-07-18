#!/usr/bin/env python
# coding: utf-8

# In[4]:


Zx.<x> = ZZ[]
p = 3
# Cyclic convolution. This is the multiplication operation used in NTRU
def convolution(f,g):
      return (f * g) % (x^n-1)

def balancedmod(f,q):
  g = list(((f[i] + q//2) % q) - q//2 for i in range(n))
  return Zx(g)


def randomdpoly(d):
  assert d <= n
  result = n*[0]
  for j in range(d):
    while True:
      r = randrange(n)
      if not result[r]: break
    result[r] = 1-2*randrange(2)
  return Zx(result)

def randompolyd1d2(d1,d2):
  assert d1 + d2 <= n
  result = n*[0]
  pos = sample(range(n),d1+d2)
  for i in pos[0:d1]:
    result[i] = 1
  for i in pos[d1:(d1+d2)]:
    result[i] = -1
  return Zx(result)

def polynorm(a):
    return(max(a.coefficients())-min(a.coefficients()))

def polynorm2(a):
    return(max(map(abs,a.coefficients())))


def invertmodprime(f,p):
    T = Zx.change_ring(Integers(p)).quotient(x^n-1)
    return Zx(lift(1 / T(f)))

# Division modulo powers of 2
def invertmodpowerof2(f,q):
    assert q.is_power_of(2)
    g = invertmodprime(f,2)
    while True:
        r = balancedmod(convolution(g,f),q)
        if r == 1: return g
        g = balancedmod(convolution(g,2 - r),q)
        
# NTRU key generation
# remember is fixed, p = 3.
def keypair():
    count = 0
    for count in range(100):
        try:
            f = randompolyd1d2(df,df-1)
            f3 = invertmodprime(f,p)
            fq = invertmodpowerof2(f,q)
            break
        except:
            pass
        assert(count < 1000)
    g = randompolyd1d2(dg,dg)
    publickey = balancedmod(p * convolution(fq,g),q)
    secretkey = f,f3
    return publickey,secretkey

def ntru_lattice(n_local = 10,df_local = 3, dg_local = 3, dphi_local = 3, q_local = 256):
    global dg,df,dphi,n,q
    dg = dg_local
    df = df_local
    dphi = dphi_local
    n = n_local
    q = q_local
    publickey,secretkey = keypair()
    recip3 =  lift(1/Integers(q_local)(3))
    publickeyover3 = (recip3 * publickey) % q
    M = matrix(2 * n)
    for i in range(n):
        M[i,i] = q
    for i in range(n):
        M[i+n,i+n] = 1
        c = convolution(x^i,publickeyover3)
        for j in range(n):
            M[i+n,j] = c[j]
    return M


# In[5]:


#print(ntru_lattice(n_local = 10, df_local = 3, dg_local = 3, dphi_local = 3, q_local = 256))


# In[6]:


from numpy import random
from math import floor, ceil, sqrt#, log

R.<x> = PolynomialRing(ZZ)


# In[24]:


#### Auxiliary functions to Ding's Genetetic Algorithm
def round_vector(vector):
    # tested okay
    return [round(v) for v in vector]

def y_to_x(y, MU):
    # tested okay
    y = vector(y)
    n = len(y)
    x = vector([0 for _ in y])
    x[n-1] = y[n-1]
    for q in range(2, n+1, 1):
        subtract = 0
        for i in range(1, q):
            subtract += x[n - q + i] * MU[n - q + i, n - q]
        x[n-q] = y[n-q] - round(subtract)
    return x

def num_to_bitstring(x, bits_length):
    # tested okay
    if x>=0:
        first_bit = '0'
    else:
        first_bit = '1'
    
    bin_rep = bin(x)[2 + (first_bit == '1'): ]
    assert len(bin_rep) < bits_length, 'bits_length is too short.'
    binstr = '0' * (bits_length - len(bin_rep) - 1) + bin_rep
    return first_bit + binstr[::-1]

def bitstring_to_num(s):
    # tested okay
    sum = 0
    for i in range(1, len(s)):
        sum += (s[i] == '1') * 2**(i-1)
    if s[0] == '1':
        sum = -sum
    return sum

def y_vector_to_bitstring(y, L):
    # tested okay
    output = ''
    assert len(y) == len(L)
    for y_elm, L_elm in zip(y, L):
        output += num_to_bitstring(y_elm, L_elm)
    return output

def bitstring_to_y_vector(b, L):
    # tested okay
    y = [0] * len(L)
    begin = 0
    for i in range(len(y)):
        y[i] = bitstring_to_num( b[ begin:(begin + L[i]) ] )
        begin += L[i]
    return y

def crossover(b1, b2):
    assert len(b1) == len(b2)
    z = zip(b1, b2)
    output = ''
    for v, w in z:
        output += random.choice([v,w])
    return output

def mutation(b):
    l = len(b)
    # change b to a list of characters to make it mutable
    b = list(b)
    for i in range(l):
        if random.random() < (1/l):
            if b[i] == '0':
                b[i] = '1'
            else:
                b[i] = '0'
    # convert b back to a string
    return ''.join(b)

def one_time_local_search(y, MU, B):
    # get y not zero, keep y not zero
    x = y_to_x(y, MU)
    v = x * B
    #vector_norm = v.norm()
    smallest_norm = v.norm()
    n = len(y)
    output = copy(y)
    y_2 = copy(y) # create as copy(.) so alteration to y_2 does not affect y
    for i in range(n):
        y_2[i] += 1
        y_2_norm = (y_to_x(y_2, MU) * B).norm()
        #print(y_2, y_2_norm)
        
        if y_2_norm < smallest_norm:
            smallest_norm = y_2_norm
            output = copy(y_2)
        
        y_2[i] -= 2        
        y_2_norm = (y_to_x(y_2, MU) * B).norm()
        #print(y_2, y_2_norm)
        
        if y_2_norm < smallest_norm:
            smallest_norm = y_2_norm
            output = copy(y_2)
        
        y_2[i] += 1
    return output

def localsearch(y, MU, B):
    # get y not zero, keep y not zero
    while True:
        new_y = one_time_local_search(y, MU, B)
        if y == new_y:
            break
        y = new_y
    return new_y
        
    
#### Generate B, basis for a lattice of NTRU type
#https://doc.sagemath.org/html/en/reference/cryptography/sage/crypto/lattice.html

# n integer, m = 2*n and quotient=x^n-1
#B = sage.crypto.gen_lattice(type='ideal', n = 3, m = 6, quotient=x^3 - 1)
"""B = matrix([[256, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], 
            [0, 256, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
           [0, 0,  256, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
           [0, 0,  0, 256, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
           [0, 0,  0, 0, 256, 0, 0, 0, 0, 0, 0, 0, 0, 0],
           [0, 0,  0, 0, 0, 256, 0, 0, 0, 0, 0, 0, 0, 0],
           [0, 0,  0, 0, 0, 0, 256, 0, 0, 0, 0, 0, 0, 0],
           [87, 130, 194, 36, 54, 210, 58, 1, 0, 0 ,0, 0, 0, 0],
           [58, 87, 130, 194, 36, 54, 210, 0, 1, 0, 0, 0, 0, 0],
           [210, 58, 87, 130, 194, 36, 54, 0, 0, 1, 0, 0, 0, 0],
           [54, 210, 58, 87, 130, 194, 36, 0, 0, 0, 1, 0, 0, 0],
           [36, 54, 210, 58, 87, 130, 194, 0, 0, 0, 0, 1, 0, 0],
           [194, 36, 54, 210, 58, 87, 130, 0, 0, 0, 0, 0, 1, 0],
           [130, 194, 36, 54, 210, 58, 87, 0, 0, 0, 0, 0, 0, 1],
           ])"""
B= ntru_lattice(n_local = 20,df_local = 6, dg_local = 6, dphi_local = 3, q_local = 256)
n = B.nrows()


# In[25]:


#### 1) BKZ-reduce B
#B = B.BKZ()

#### 2) Get GS-Basis and mu's coefficients from B
B_GSO, MU = B.gram_schmidt()

## Calculate l_0, l_1, ...
#L = [max(2, 2 +  floor(log(B_GSO[0].norm()/B_GSO[i].norm(), 2))) for i in range(n)]
print(B)
#L = [2]


# In[9]:


"""print(B, "\n")

v = vector([10,1,2,3,4,5,6,7,8,7,6,5,4,3])
B2 = B

B2[0] = v
print(B2)
print('type(B2) = ', type(B2))
print('type(B2[0]) = ', type(B2[0]))
print('type(v) = ', type(v))
"""

"""
B = B.BKZ()
print('B = ', B, '\n')
print('MU = ', MU, '\n')
v = vector(random.choice([-3, -2, -1, 0, 1, 2, 3], size=14, replace=True)) * B
print('v = ', v, '\n')

x = v * (B**-1)
print('x = ', x, '\n')

v = x * B
print('v = ', v, '\n')

y = vector(round_vector(x * MU))
print('y = ', y, '\n')

x = y_to_x(y, MU)
print('x = ', x, '\n')

L = vector(random.choice([4, 5, 6, 7, 8], size=14, replace=True))
b = y_vector_to_bitstring(y, L); print('b = ', b, '\n')
y = vector(bitstring_to_y_vector(b, L)); print('         y = ', y, '\n')

y2 = y; print('         y = ', y, '   v = ', v, '  norm = ', v.norm())

y = localsearch(y, MU, B);
v = (y_to_x(y, MU) * B)
print('improved y = ', y, '   v = ', v,  '  norm = ', v.norm())"""


# In[10]:


"""y = vector((-4, -6, -1, 0, -8, 1, -5, 0, -1, -3, 0, 0, 0, -3) ); print(y, y.norm())
x = y_to_x(y, MU); print(x)
v = x * B; print(v)
n = len(y); print(n)
output = y; print(output)
y_2 = copy(y); print(y_2)
print('\n\n\n')

i = 0
y_2[0] = y[0] + 1; print(y_2, y)
y_2_norm = (y_to_x(y_2, MU) * B).norm() ; print(y_2_norm)

y_2[0] = y[0] - 1; print(y_2, y)"""

#vector((-50, -5, 37, -28, 20, 12, 11, 36, -19, 45, 6, -32, -20, -19)) * B**-1


# In[11]:


"""y = vector((68, 3, 0, 1, 7, 5, 5, 5, 6, 3, 3, 3, -1, 2)) 
print(y, type(y))

y = vector(y)
print(y, type(y))
n = len(y); print(n)
x = vector([0 for _ in y]); print(x, type(x))
x[n-1] = y[n-1]; print(x)

print('MU = \n', MU)

q = 2
i = 1
subtract = 0
subtract += x[n-i] * MU[n-q, n-i]
print(subtract)
x[n-q] = y[n-q] - round(subtract)
print(x)"""


# In[20]:


print(B,'\n')
#print(B_GSO,'\n')


# In[26]:


#### 3) Creates initial population of size 2*n
popsize = 2*n
B_inv   = B**-1

# V has the vectors in Z^n coordinates
V = matrix([(-1)**(i >= n) * B[i % n] for i in range(popsize)])

#### 4) Exchange the individuals of P in order according to ther euclidian norms
# V has the vectors in Z^n coordinates
# X has the vectors in base B coordinates
# Y has the vectors in pseudo-base B_GSO coordinates

###V = matrix(sorted(V, key = norm))

# X has the vectors in base B coordinates
X = matrix([v * B_inv for v in V])

# Y has the vectors in pseudo-base B_GSO coordinates
Y = matrix([round_vector(x * MU) for x in X])

max_abs_entry = 0
for i in range(n):
    for j in range(n):
        max_abs_entry = max(max_abs_entry, abs(Y[i,j]))

#L = [1+ceil(log(max_abs_entry+1,2)) for _ in range(n)]
L = [5 for _ in range(n)]

B_inv = B**-1


# In[27]:


print(V, '\n\n\n', X, '\n\n\n', Y)


# In[28]:


#### 5) Loop until short vector is found
# references: https://doc.sagemath.org/html/en/reference/probability/sage/probability/probability_distribution.html
#x1 = X[0]; v0 = x1 * B; v0 = V[0]
iteration = 0

while V[0].norm() > sqrt(n/2+5) and iteration < 1000: # use later '> Gaussian-heuristic for SVP'
    new_pop_V = matrix(ZZ, popsize, n, 0)
    new_pop_X = matrix(ZZ, popsize, n, 0)
    new_pop_Y = matrix(ZZ, popsize, n, 0)
    
    # (a) (k) variable keeps track of how many new individuals we have made in this iteration
    k = 0
    # (b) creates prob. dist. proportional to the inverse of squared euclidean norms
    ProbDist = [(v.norm())**(-2) for v in V]
    ProbDist = [p / sum(ProbDist) for p in ProbDist]
    #print('Y= ', Y)
    while True:
        
        i, j = random.choice(range(popsize), size=2, p=ProbDist, replace=False)
        # (c) apply, to the selected pair, vector-to-bits-conversion, crossover and mutation
        while True:
            #print('k= ', k, 'Y[i] = ', Y[i], '   Y[j] = ', Y[j])
            b = mutation(crossover(y_vector_to_bitstring(Y[i], L), y_vector_to_bitstring(Y[j], L)))
            #print('b = ', b)
            # (d) convert b to a vector of type-y and type-x
            new_y = bitstring_to_y_vector(b, L)
            new_y = localsearch(new_y, MU, B)
            #print('new_y =', new_y)
            assert all(abs(el) <= 31 for el in new_y)
            new_x = y_to_x(new_y, MU)
            if (any(el != 0 for el in new_x)):
                new_x = matrix(ZZ, new_x)
                new_pop_V[k] = new_x * B
                new_pop_X[k] = new_x
                new_pop_Y[k] = new_y
                break
        # (e) update k by 1, as 1 individual has been added to the new generation
        k += 1
        #     now k points to the next empty box
        if k == popsize - 1 :
            break
    
    # here k == popsize
    new_pop_V[k] = V[0] # keep the previous best according to elitist strategy
    new_pop_X[k] = X[0]
    new_pop_Y[k] = Y[0]
    
    # order V according to euclidean norm and updates its X- and Y- coordinates
    euclidean_norms = [v.norm() for v in V]
    V = matrix(sorted(new_pop_V, key = norm))
    #X = V * B_inv
    #Y = [round_vector(x * MU) for x in X]
    X = matrix([val for (_, val) in sorted(zip(euclidean_norms, new_pop_X), key=lambda x: x[0])])
    Y = matrix([val for (_, val) in sorted(zip(euclidean_norms, new_pop_Y), key=lambda x: x[0])])
    iteration += 1
    print('iter = ', iteration, 'curr. SVP = ', V[0],'   norm = ', V[0].norm())

print(V[0])


# In[17]:


#vector((1, -1, 0, 0, 1, 1, -1, 1, -1, 0, 0, 1, -1, 1)) * (B**-1)


# In[13]:


B


# In[ ]:


#new_B = copy(B)
#B_GSO, mu = GS(new_B)
#print(B_GSO)
#print(mu)


# In[255]:


# create initial population
#P = matrix(2*n, n, 0)
#for i in range(2*n):
#    P[i] = (-1)**(i >= n) * B[i % n]


# In[256]:


#S = [B[i].norm() for i in range(n)]; S


# In[233]:


#print(P); print(sorted(P))


# In[230]:


S


# In[ ]:





# In[ ]:





# In[ ]:





# In[21]:


sqrt(45)


# In[204]:





# In[193]:





# In[120]:





# In[176]:





# In[195]:





# In[196]:





# In[197]:





# In[424]:





# In[ ]:




