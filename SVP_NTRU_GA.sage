#!/usr/bin/env python
# coding: utf-8

# In[5]:


### funções Thiago:

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


# In[6]:


from numpy import random
from math import floor, ceil, sqrt#, log

R.<x> = PolynomialRing(ZZ)


# In[63]:


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

def cost_x(x):
    e = x - round_vector(x)
    return vector((abs(w) for w in e))

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
    
    
    
    
    
    
    """x = v * B_inv
    cur_cost = cost_x(x)
    min_cost_x = x
    n = len(v)
    
    
    for i in range(n):
        x_cand = x + B[i]
        if cost_x(x_cand) < cur_cost:
            cur_cost = cost_x(x_cand)
            min_cost_x = x_cand
        x_cand = x - B[i]
        if cost_x(x_cand) < cur_cost:
            cur_cost = cost_x(x_cand)
            min_cost_x = x_cand
        
    return min_cost_x"""
    
    """
    initial_cost = cur_cost
    
    v2 = copy(v)
    output = copy(v)
    #all_modifications = vector([0 for _ in range(n)])
    gradient_direction = copy(v)
    
    for i in range(n):
        # add 1 to v2[i]'s original value
        v2[i] = sum_mod3_centered(v[i], 1)
        v2cost = cost(v2, B_inv)
        
        if v2cost < initial_cost:
            gradient_direction[i] = sum_mod3_centered(gradient_direction[i], 1)
            if v2cost < cur_cost:
                cur_cost = v2cost
                output = copy(v2)
            
        
        # subtract 1 to v2[i]'s original value
        v2[i] = sum_mod3_centered(v[i], -1)       
        v2cost = cost(v2, B_inv)
        
        if v2cost < initial_cost:
            gradient_direction[i] = sum_mod3_centered(gradient_direction[i], -1)
            if v2cost < cur_cost:
                cur_cost = v2cost
                output = copy(v2)
        
        # reset v2[i] to it's original value
        v2[i] = v[i]
    
    #gradient_direction = vector( ( sum_mod3_centered(v[i], all_modifications[i]) for i in range(n) ) )
    cost_gradient  = cost(gradient_direction, B_inv)
    if cost_gradient < cur_cost:
        output = gradient_direction
        cur_cost = cost_gradient
        
    shift1 = vector(  ( sum_mod3_centered(v[i], 1)  for i in range(n) ) )
    cost_shift1  = cost(shift1, B_inv)
    if cost_shift1 < cur_cost:
        output = shift1
        cur_cost = cost_shift1
    
    shift2 = vector(  ( sum_mod3_centered(v[i], 2)  for i in range(n) ) )
    cost_shift2  = cost(shift2, B_inv)
    if cost_shift2 < cur_cost:
        output = shift2
        cur_cost = cost_shift2
    
    
    
    return output
    """

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
        
    


# In[114]:


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
B = ntru_lattice(n_local = 10, df_local = 5, dg_local = 4, dphi_local = 12, q_local = 256)
n = B.nrows()
#B = B.LLL()
B_inv = B**-1
print(n, '\n', B, '\n\n\n', B.BKZ())


# In[99]:


def SVP_RT(B):
    print("starting new try")
    n = B.nrows()
    B_inv = B**-1
    popsize = 2*n
    pop = matrix(ZZ, popsize, n, 0)
    for i in range(popsize):
        pop[i] = vector(random.choice((-1,0,1), size=n, replace=True))
    cost_values = vector(QQ, (0 for _ in range(popsize)))
    for i in range(popsize):
        cost_values[i] = cost(pop[i], B_inv)
    # order pop by increasing cost_values and sort cost_value
    pop = matrix([val for (_, val) in sorted(zip(cost_values, pop), key=lambda x: x[0])])
    cost_values = vector(sorted(cost_values))
    if cost_values[0] == 0:
        return pop[0]
    inv_cost = vector( (1/x for x in cost_values) )
    
    iterations_without_improvement = 0
    smallest_cost = cost_values[0]
    
    random_slice = 0 #popsize // 2
    
    # initialize matrix that will contain each newly generated population
    new_pop = matrix(ZZ, popsize, n, 0)
    while iterations_without_improvement < 2*n:
        
        inv_cost = vector( (1/x for x in cost_values) )
        for q in range(0 ,popsize - 1 - random_slice):
            # select pair proportional to fitness
            #i, j = random.choice(range(popsize), size=2, p=inv_cost/sum(inv_cost), replace=False)
            # cross, mutation and localsearch
            #new_pop[q] = localsearch(mutation(crossover(pop[i], pop[j])), B_inv)
            # select pair proportional to fitness
            #i, j = random.choice(range(popsize), size=2, p=inv_cost/sum(inv_cost), replace=False)
            j = random.choice(range(popsize), size =1, p=inv_cost/sum(inv_cost), replace=False)
            new_pop[q] = localsearch(mutation(copy(pop[j])), B_inv)
            #new_pop[q] = localsearch(mutation(crossover(pop[i], pop[j])), B_inv)
        
        for q in range(popsize - 1 - random_slice, popsize - 1):
            new_pop[q] = localsearch(vector(random.choice((-1,0,1), size=n, replace=True)), B_inv)
        
        new_pop[popsize-1] = pop[0]
        pop = copy(new_pop)
        # order pop by increasing cost_values and sort cost_values
        for i in range(popsize):
            cost_values[i] = cost(pop[i], B_inv)
        pop = matrix([val for (_, val) in sorted(zip(cost_values, pop), key=lambda x: x[0])])
        cost_values = vector(sorted(cost_values))
        if cost_values[0] == 0:
            return pop[0]
        
        new_smallest_cost = cost_values[0]
        if new_smallest_cost == smallest_cost:
            iterations_without_improvement += 1
            print('_', iterations_without_improvement, end='')
        else:
            print('\n', pop[0], cost_values[0], 'advancing took ', 1+iterations_without_improvement, ' iterations.')
            iterations_without_improvement = 0
        
        smallest_cost = new_smallest_cost
        
    return vector(ZZ, (0 for _ in range(popsize)))


# In[100]:


import time
start = time.time()
print('n = ', n)
v = SVP_RT(B)
while min(v) == max(v):
    v = SVP_RT(B)
    
print('\nSVP =', v)
print('SVP coordinates =', v*B_inv)
end = time.time(); print('seconds passed: ', round(end - start, 2))


# In[75]:


a = crossover(vector((1,0,0,-1,0,1,0,-1,1)), vector((-1,-1,0,0,-1,0,1,1,-1))); print(a); print(type(a))

b = mutation(a); print(b); print(type(b))

c = mutation(vector((1,0,0,-1,0,1,0,-1,1)) ); print(c); print(type(c))



# In[17]:


v


# In[18]:


B


# In[29]:


n = len(v); print(n)
B = B_inv**-1; print(B)
D = v * B_inv - round_vector(v * B_inv); print(D)
D = vector( (abs(D[i]) * B[i].norm()  for i in range(n)) ) ; print(D)
d = sum(D); print(d)


# In[ ]:




