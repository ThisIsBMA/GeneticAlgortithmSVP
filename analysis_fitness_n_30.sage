#!/usr/bin/env python
# coding: utf-8

# In[16]:


# Analysis of fitness function


# In[17]:


### funções Thiago:
global_poly_f = None
global_poly_g = None

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
    #for count in range(10000):
    while True:
        try:
            f = randompolyd1d2(df,df-1)
            f3 = invertmodprime(f,p)
            fq = invertmodpowerof2(f,q)
            break
        except:
            pass
        #assert(count < 1000)
    
    g = randompolyd1d2(dg,dg)
    publickey = balancedmod(p * convolution(fq,g),q)
    secretkey = f,f3
    global global_poly_f
    global global_poly_g
    global_poly_f = f
    global_poly_g = g
    print('(g,f) = ', (g,f))
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
    #return M
    return M


# In[18]:


from numpy import random
from math import floor, ceil, sqrt#, log

R.<x> = PolynomialRing(ZZ)


# In[19]:


#### Auxiliary functions to RT's Genetetic Algorithm for NTRU Lattices
def sum_mod3_centered(x, y):
    # x, y in [-1,0,1]
    return (x + 1 + y) % 3 - 1

def round_vector(myvec):
    # tested okay
    return vector([round(v) for v in myvec])

def crossover(v1, v2):
    #v1 and v2 sage vectors
    l = len(v1)
    assert l == len(v2)
    z = zip(v1, v2)
    output = vector( (0 for _ in range(l)) )
    i = 0
    for a, b in z:
        output[i] = random.choice((a, b))
        i += 1
    return output

def mutation(v):
    # v sage vector
    l = len(v)
    for i in range(l):
        r = random.random() # r <- random uniform(0,1)
        if r  < 1/l:
            # plus 1
            v[i] = ( (v[i] + 2) % 3) - 1
        elif r < 2/l:
            # minus 1
            v[i] = (v[i] % 3) - 1
            
    return v

def cost(v, B_inv):
    #n = len(v)
    #B = B_inv**-1
    #B_norms = vector( (B[i].norm() for i in range(n)) )
    d = v * B_inv - round_vector(v * B_inv)
    
    #D = vector( (abs(D[i]) * B[i].norm()  for i in range(n)) )
    #d = sum(D)
    return d*d # previously d*d

#def cost_x(x):
#    e = x - round_vector(x)
#    return vector((abs(w) for w in e))

def one_time_local_search(v, B_inv):
    cur_cost = cost(v, B_inv)
    n = len(v)
    v2 = copy(v)
    output = copy(v)
    
    for i in range(n):
        v2[i] = ( (v[i] + 2) % 3) - 1
        v2cost = cost(v2, B_inv)
        
        if v2cost < cur_cost:
            cur_cost = v2cost
            output = copy(v2)
        
        v2[i] = (v[i] % 3) - 1        
        v2cost = cost(v2, B_inv)
        
        if v2cost < cur_cost:
            cur_cost = v2cost
            output = copy(v2)
        
        v2[i] = v[i]
    return output   

def localsearch(v, B_inv):
    # get y not zero, keep y not zero
    while True:
        new_v = one_time_local_search(v, B_inv)
        if v == new_v:
            break
        v = new_v
    return new_v

#def localsearch(x):
    
def one_time_tabu_search(v, B_inv, tabu):
    cur_cost = +Infinity
    #initial_cost = cur_cost
    n = len(v)
    v2 = copy(v)
    output = copy(v)
    
    for i in range(n):
        # add 1 to v2[i]'s original value
        v2[i]  = sum_mod3_centered(v[i], 1)
        if v2 not in tabu:
            v2cost = cost(v2, B_inv)
            if v2cost < cur_cost:
                cur_cost = v2cost
                output   = copy(v2)
            
        # subtract 1 to v2[i]'s original value
        v2[i] = sum_mod3_centered(v[i], -1)
        if v2 not in tabu:
            v2cost = cost(v2, B_inv)
            if v2cost < cur_cost:
                cur_cost = v2cost
                output   = copy(v2)
        
        # reset v2[i] to it's original value
        v2[i] = v[i]
    return output

def tabusearch(v, B_inv):
    tabu = [v]
    #print('tabu = ', tabu)
    n = len(v)
    best_of_all = v
    smallest_cost = cost(v, B_inv)
    for q in range(2*n):
        best = one_time_tabu_search(v, B_inv, tabu)
        if best == v:
            return v
        new_cost = cost(best, B_inv)
        if new_cost < smallest_cost:
            smallest_cost = new_cost
            best_of_all = best
        v = best
        tabu += [v]
        #print('len tabu = ', len(tabu))
    #print('leaving tabusearch')
    return v


# In[76]:


B = ntru_lattice(n_local = 50, df_local = 13, dg_local = 13, dphi_local = 12, q_local = 256)
B_inv = B**-1; print(B_inv)

print(vector(global_poly_g).list())

print(vector(global_poly_f).list())


# complete the vectors with 0's if necessary (the case polynomial has degree less than n-1)
poly_g = vector(global_poly_g).list()
poly_f = vector(global_poly_f).list()
if len(poly_g) < n:
    poly_g = poly_g + [0 for i in range(n - len(poly_g))]
if len(poly_f) < n:
    poly_f = poly_f + [0 for i in range(n - len(poly_f))]

#s = vector( vector(global_poly_g).list() + vector(global_poly_f).list() ); print( 's = ', s ); print(type(s))
s = vector(poly_g + poly_f); print('s = ', s); print('len(s) = ', len(s)); print('s*B_inv = ', s*B_inv)


# In[77]:


n = B.nrows()
#B = B.LLL()

print(n, '\n', B, '\n\n\n', B.BKZ(), '\n\n')



#secrets = vector(vector(global_poly_g).list() + vector(global_poly_f).list())
#print(secrets)
#print(secrets * B_inv)
#print('secretpair = ', secretpair)
#print(list(secretpair))


# In[78]:


B_BKZ = copy(B.BKZ())
#solution = B_BKZ[n//2 -1]; print(solution, '\n\n')
solution = s; print(solution, '\n\n')

B_inv = B ** -1
# set of vectors that are distinct from 'solution' in 1 element

neigh1 = matrix([solution for i in range(2*n)]); #print(neigh1, '\n\n')
#cpneigh1 = copy(neigh1)

k = 0
for i in range(n):
    for j in (1,2):
        #print('k = ', k)
        neigh1[k, k//2] = (solution[k//2] + 1 + j) % 3 - 1
        k += 1
    
print(neigh1)

B_BKZ_inv = B_BKZ**-1


# In[23]:


""""sample_size = 1000
cost_neigh_no_bkz_2  = [-1 for i in range(sample_size)]
cost_neigh_yes_bkz_2 = [-1 for i in range(sample_size)]

##### costs WITHOUT and WITH BKZ for Hammind distance of 1
for i in range(sample_size):
    #print(cost(neigh1[i], B_inv))
    cost_neigh_no_bkz_2[i] = cost(neigh1[i], B_inv)

print("\n")
for i in range(sample_size):
    #print(cost(neigh1[i], B_BKZ_inv))
    cost_neigh_yes_bkz_2[i] = cost(neigh1[i], B_BKZ_inv)
    
# plot histogram 
import matplotlib.pyplot as plt
plt.hist([cost_neigh_no_bkz_2,cost_neigh_yes_bkz_2], bins='auto', edgecolor='black', density = False,  label=['NO bkz', 'YES bkz'])
plt.xlabel('Cost')
plt.ylabel('Frequency')
plt.legend()
plt.savefig('hist_full_range.png', dpi=300)
plt.show()"""

sample_size = 10000
cost_neigh_no_bkz_1  = [-1 for i in range(sample_size)]
cost_neigh_yes_bkz_1 = [-1 for i in range(sample_size)]

import matplotlib.pyplot as plt
##### costs WITHOUT and WITH BKZ for Hammind distance of 1
print("Ham. dist. of 1:")
hd = 1
neigh1 = matrix([solution for i in range(sample_size)]); print(type(neigh1))

# the 'sample' method returns a list object. Using sample(tuple/list , n)[0] to get the first element of the output
for i in range(sample_size):
    rvec = sample(range(n), hd)
    for r in rvec:
        #print('i = ', i, '  ||    r = ', r)
        neigh1[i, r] = (neigh1[i, r] + 1 + sample((-1, 1), 1)[0]) % 3 - 1
    
    cost_neigh_no_bkz_1[i] = cost(neigh1[i], B_inv)
    cost_neigh_yes_bkz_1[i]   = cost(neigh1[i], B_BKZ_inv)
    
# plot histogram
plt.hist([cost_neigh_no_bkz_1,cost_neigh_yes_bkz_1], bins='auto', edgecolor='black', density = False,  label=['NO bkz', 'YES bkz'])
plt.xlabel('Cost')
plt.ylabel('Frequency')
plt.legend()
plt.title('lattice dim. = 30, sample size = 10000, Ham. dist. = 1')
plt.savefig('hist_full_range.png', dpi=300)
plt.show()


# In[24]:


sample_size = 10000
cost_neigh_no_bkz_2  = [-1 for i in range(sample_size)]
cost_neigh_yes_bkz_2 = [-1 for i in range(sample_size)]

##### costs WITHOUT and WITH BKZ for Hammind distance of 2
print("Ham. dist. of 2:")
hd = 2
neigh1 = matrix([solution for i in range(sample_size)]); print(type(neigh1))

# the 'sample' method returns a list object. Using sample(tuple/list , n)[0] to get the first element of the output
for i in range(sample_size):
    rvec = sample(range(n), hd)
    for r in rvec:
        #print('i = ', i, '  ||    r = ', r)
        neigh1[i, r] = (neigh1[i, r] + 1 + sample((-1, 1), 1)[0]) % 3 - 1
    
    cost_neigh_no_bkz_2[i] = cost(neigh1[i], B_inv)
    cost_neigh_yes_bkz_2[i]   = cost(neigh1[i], B_BKZ_inv)
    
# plot histogram
plt.hist([cost_neigh_no_bkz_2,cost_neigh_yes_bkz_2], bins='auto', edgecolor='black', density = False,  label=['NO bkz', 'YES bkz'])
plt.xlabel('Cost')
plt.ylabel('Frequency')
plt.legend()
plt.title('lattice dim. = 30, sample size = 10000, Ham. dist. = 2')
plt.savefig('hist_full_range.png', dpi=300)
plt.show()


# In[26]:


sample_size = 10000
cost_neigh_no_bkz_3  = [-1 for i in range(sample_size)]
cost_neigh_yes_bkz_3 = [-1 for i in range(sample_size)]

##### costs WITHOUT and WITH BKZ for Hammind distance of 3
print("Ham. dist. of 3:")
hd = 3
neigh1 = matrix([solution for i in range(sample_size)]); print(type(neigh1))

# the 'sample' method returns a list object. Using sample(tuple/list , n)[0] to get the first element of the output
for i in range(sample_size):
    rvec = sample(range(n), hd)
    for r in rvec:
        #print('i = ', i, '  ||    r = ', r)
        neigh1[i, r] = (neigh1[i, r] + 1 + sample((-1, 1), 1)[0]) % 3 - 1
    
    cost_neigh_no_bkz_3[i] = cost(neigh1[i], B_inv)
    cost_neigh_yes_bkz_3[i]   = cost(neigh1[i], B_BKZ_inv)
    
# plot histogram
plt.hist([cost_neigh_no_bkz_3,cost_neigh_yes_bkz_3], bins='auto', edgecolor='black', density = False,  label=['NO bkz', 'YES bkz'])
plt.xlabel('Cost')
plt.ylabel('Frequency')
plt.legend()
plt.title('lattice dim. = 30, sample size = 10000, Ham. dist. = 3')
plt.savefig('hist_full_range.png', dpi=300)
plt.show()


# In[27]:


sample_size = 10000
cost_neigh_no_bkz_4  = [-1 for i in range(sample_size)]
cost_neigh_yes_bkz_4 = [-1 for i in range(sample_size)]

##### costs WITHOUT and WITH BKZ for Hammind distance of 4
print("Ham. dist. of 4:")
hd = 4
neigh1 = matrix([solution for i in range(sample_size)]); print(type(neigh1))

# the 'sample' method returns a list object. Using sample(tuple/list , n)[0] to get the first element of the output
for i in range(sample_size):
    rvec = sample(range(n), hd)
    for r in rvec:
        neigh1[i, r] = (neigh1[i, r] + 1 + sample((-1, 1), 1)[0]) % 3 - 1
    
    cost_neigh_no_bkz_4[i] = cost(neigh1[i], B_inv)
    cost_neigh_yes_bkz_4[i]   = cost(neigh1[i], B_BKZ_inv)
    
# plot histogram
plt.hist([cost_neigh_no_bkz_4,cost_neigh_yes_bkz_4], bins='auto', edgecolor='black', density = False,  label=['NO bkz', 'YES bkz'])
plt.xlabel('Cost')
plt.ylabel('Frequency')
plt.legend()
plt.title('lattice dim. = 30, sample size = 10000, Ham. dist. = 4')
plt.savefig('hist_full_range.png', dpi=300)
plt.show()


# In[28]:


sample_size = 10000
cost_neigh_no_bkz_5  = [-1 for i in range(sample_size)]
cost_neigh_yes_bkz_5 = [-1 for i in range(sample_size)]

##### costs WITHOUT and WITH BKZ for Hammind distance of 5
print("Ham. dist. of 5:")
hd = 5
neigh1 = matrix([solution for i in range(sample_size)]); print(type(neigh1))

# the 'sample' method returns a list object. Using sample(tuple/list , n)[0] to get the first element of the output
for i in range(sample_size):
    rvec = sample(range(n), hd)
    for r in rvec:
        neigh1[i, r] = (neigh1[i, r] + 1 + sample((-1, 1), 1)[0]) % 3 - 1
    
    cost_neigh_no_bkz_5[i] = cost(neigh1[i], B_inv)
    cost_neigh_yes_bkz_5[i]   = cost(neigh1[i], B_BKZ_inv)
    
# plot histogram
plt.hist([cost_neigh_no_bkz_5,cost_neigh_yes_bkz_5], bins='auto', edgecolor='black', density = False,  label=['NO bkz', 'YES bkz'])
plt.xlabel('Cost')
plt.ylabel('Frequency')
plt.legend()
plt.title('lattice dim. = 30, sample size = 10000, Ham. dist. = 5')
plt.savefig('hist_full_range.png', dpi=300)
plt.show()


# In[29]:


sample_size = 10000
cost_neigh_no_bkz_6  = [-1 for i in range(sample_size)]
cost_neigh_yes_bkz_6 = [-1 for i in range(sample_size)]

##### costs WITHOUT and WITH BKZ for Hammind distance of 5
print("Ham. dist. of 6:")
hd = 6
neigh1 = matrix([solution for i in range(sample_size)]); print(type(neigh1))

# the 'sample' method returns a list object. Using sample(tuple/list , n)[0] to get the first element of the output
for i in range(sample_size):
    rvec = sample(range(n), hd)
    for r in rvec:
        neigh1[i, r] = (neigh1[i, r] + 1 + sample((-1, 1), 1)[0]) % 3 - 1
    
    cost_neigh_no_bkz_6[i] = cost(neigh1[i], B_inv)
    cost_neigh_yes_bkz_6[i]   = cost(neigh1[i], B_BKZ_inv)
    
# plot histogram
plt.hist([cost_neigh_no_bkz_6,cost_neigh_yes_bkz_6], bins='auto', edgecolor='black', density = False,  label=['NO bkz', 'YES bkz'])
plt.xlabel('Cost')
plt.ylabel('Frequency')
plt.legend()
plt.title('lattice dim. = 30, sample size = 10000, Ham. dist. = 6')
plt.savefig('hist_full_range.png', dpi=300)
plt.show()


# In[79]:


sample_size = 10000
matrix_cost_neigh_no_bkz  = matrix(QQ, [[-1 for i in range(1, n)] for j in range(sample_size)])
matrix_cost_neigh_yes_bkz = matrix(QQ, [[-1 for i in range(1, n)] for j in range(sample_size)])
print( matrix_cost_neigh_yes_bkz.nrows(), matrix_cost_neigh_yes_bkz.ncols() )

##### costs WITHOUT and WITH BKZ for multiple Hamming distances
for ham_dist in range(1, n):
    neigh1 = matrix([solution for i in range(sample_size)])
    # the 'sample' method returns a list object. Using sample(tuple/list , n)[0] to get the first element of the output
    for i in range(sample_size):
        rvec = sample(range(n), ham_dist)
        for r in rvec:
            neigh1[i, r] = (neigh1[i, r] + 1 + sample((-1, 1), 1)[0]) % 3 - 1
        #print('i = ', i)
        matrix_cost_neigh_no_bkz[i, ham_dist - 1]  = cost(neigh1[i], B_inv)
        matrix_cost_neigh_yes_bkz[i, ham_dist - 1] = cost(neigh1[i], B_BKZ_inv)


# In[80]:


plt.boxplot(list(matrix_cost_neigh_no_bkz.transpose()))


# In[81]:


plt.boxplot(list(matrix_cost_neigh_yes_bkz.transpose()))


# In[85]:


plt.figure(figsize=(24, 8))  # Set the figure size (width, height)
plt.boxplot(list(matrix_cost_neigh_no_bkz.transpose()))


# In[84]:


plt.figure(figsize=(24, 8))  # Set the figure size (width, height)
plt.boxplot(list(matrix_cost_neigh_yes_bkz.transpose()))


# In[107]:


import seaborn as sns
import matplotlib.pyplot as plt
import numpy as np

# Sample data
#data = np.random.normal(loc=0, scale=1, size=1000)
data = list(matrix_cost_neigh_yes_bkz.transpose())[0]
data = np.array(data)
print(data)
# Plot KDE
sns.kdeplot(data, fill=True)  # Use fill=True for a shaded plot
plt.title("Kernel Density Estimate (KDE)")
plt.xlabel("Value")
plt.ylabel("Density")
plt.grid(True)
plt.show()


# In[126]:


import seaborn as sns
import matplotlib.pyplot as plt
import pandas as pd
import numpy as np

data = list(matrix_cost_neigh_no_bkz.transpose())
data = data[0:50]

# Create sample data
np.random.seed(0)
df = pd.DataFrame({
    'Cost Value': np.concatenate(data),
    'Hamming Distance': [str(x) for x in range(1, 51) for i in range(sample_size)]
})

# Plot multiple violin plots
plt.figure(figsize=(35, 8))
sns.violinplot(x='Hamming Distance', y='Cost Value', data=df, inner='box', palette='Set2')
plt.title("Using Original Basis: Distribution of Hamming Distances X Cost Values")
plt.grid(True)
plt.show()


# In[124]:


import seaborn as sns
import matplotlib.pyplot as plt
import pandas as pd
import numpy as np

data = list(matrix_cost_neigh_yes_bkz.transpose())
data = data[0:50]

# Create sample data
np.random.seed(0)
df = pd.DataFrame({
    'Cost Value': np.concatenate(data),
    'Hamming Distance': [str(x) for x in range(1, 51) for i in range(sample_size)]
})

# Plot multiple violin plots
plt.figure(figsize=(35, 8))
sns.violinplot(x='Hamming Distance', y='Cost Value', data=df, inner='box', palette='Set2')
plt.title("Using BKZ-reduced Basis: Distribution of Hamming Distances X Cost Values")
plt.grid(True)
plt.show()


# In[ ]:


sample_size = 100

n = 100 #dimension of lattices
matrix_cost_neigh_no_bkz  = matrix(QQ, [[-1 for i in range(1, n)] for j in range(sample_size)])
matrix_cost_neigh_yes_bkz = matrix(QQ, [[-1 for i in range(1, n)] for j in range(sample_size)])
print( matrix_cost_neigh_yes_bkz.nrows(), matrix_cost_neigh_yes_bkz.ncols() )


##### costs WITHOUT and WITH BKZ for multiple Hamming distances
for ham_dist in range(1, n):    
    #neigh1 = matrix([solution for i in range(sample_size)])
    # the 'sample' method returns a list object. Using sample(tuple/list , n)[0] to get the first element of the output
    for i in range(sample_size):
        # generates new lattice basis for every sample, with corresponding (g,f) secret pair
        B = ntru_lattice(n_local = n//2, df_local = n//3, dg_local = n//3, dphi_local = 12, q_local = 256)
        B_inv = B**-1; B_BKZ_inv = B.BKZ() ** -1
        # complete the vectors with 0's if necessary (the case polynomial has degree less than n-1)
        poly_g = vector(global_poly_g).list(); poly_f = vector(global_poly_f).list()
        if len(poly_g) < n:
            poly_g = poly_g + [0 for i in range(n - len(poly_g))]
        if len(poly_f) < n:
            poly_f = poly_f + [0 for i in range(n - len(poly_f))]
        solution = vector(poly_g + poly_f)#; print('s = ', s); print('len(s) = ', len(s)); print('s*B_inv = ', s*B_inv)
        rvec = sample(range(n), ham_dist)
        for r in rvec:
            solution[r] = (solution[r] + 1 + sample((-1, 1), 1)[0]) % 3 - 1
        #print('i = ', i)
        matrix_cost_neigh_no_bkz[i, ham_dist - 1]  = cost(neigh1[i], B_inv)
        matrix_cost_neigh_yes_bkz[i, ham_dist - 1] = cost(neigh1[i], B_BKZ_inv)


# In[38]:





# In[ ]:


# Example data: list of datasets
data = [
    cost_neigh_yes_bkz_1, cost_neigh_yes_bkz_2, cost_neigh_yes_bkz_3, cost_neigh_yes_bkz_4, cost_neigh_yes_bkz_5, cost_neigh_yes_bkz_6
]

plt.boxplot(data)
plt.xticks([1, 2, 3, 4, 5, 6], ['H.D. 1', 'H.D. 2', 'H.D. 3', 'H.D. 4', 'H.D. 5', 'H.D. 6'])
plt.title('With BKZ-reduction')
plt.ylabel('Cost Values')
plt.show()


# In[ ]:





# In[ ]:




