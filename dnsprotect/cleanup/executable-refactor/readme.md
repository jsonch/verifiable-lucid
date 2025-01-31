1/30/25

This version supports both verification and execution over sequences using a generic Interpreter class.


Problem: 

The operating assumptions might not make sense. 

Consider a high-rate attack (packets per interval > U > L) that lasts much longer than T. 

What happens? 

t=0:    Attack starts, rate > U
t=x:    Filtering turns on, actualTimeOn = x
t=x+T:  Attack still ongoing, but now time >= actualTimeOn + T
t>x+T:  Any packet violates operatingAssumptions:
    (filtering.val ==> time < actualTimeOn + T)

So it seems like an attack that lasts sufficiently longer than T is outside the operatingAssumptions of the defense? That doesn't feel right.


```
# Analysis of Attack vs Operating Assumptions

1. **Timeline of Attack**
```
t=0:    Attack starts, rate > U
t=x:    Filtering turns on, actualTimeOn = x
t=x+T:  Attack still ongoing, but now time >= actualTimeOn + T
t>x+T:  Any packet violates operatingAssumptions
```

2. **Key Points**
- Filtering won't turn off because:
  - Rate exceeds L
  - timeOn keeps getting reset
  - Never reaches Q + Roff time with low counts
- But operatingAssumptions requires:
  - `filtering.val ==> time < actualTimeOn + T`
- actualTimeOn doesn't get updated unless filtering turns off and on again

3. **Conclusion**
Yes, you're correct. This reveals a disconnect:
- System can maintain filtering indefinitely (by resetting timeOn)
- But operatingAssumptions assumes all packets arrive within T of initial filtering activation
- Long attacks will violate this assumption

This suggests either:
- Operating assumptions need revision to handle persistent attacks
- Or system needs mechanism to reset actualTimeOn periodically
```