def mahler_coefs(f,maxn):
    if len(f.variables())==0:
        const = true 
    else:
        z = f.variables()[0]
        const = false
    if not const:
        v = [f.substitute(z=i) for i in range(maxn+1)]
    else:
	v = [f for i in range(maxn+1)]
    ans = []
    for m in range(maxn+1):
    	c = sum([(-1)^(m-i)*binomial(m,i)*v[i] for i in range(m+1)])
	ans.append(c)
    return ans