# Eulers-Totient-ACL2-Proof
An ACL2s proof of Euler's Totient function being bound above by n

```bash
(defthm bbn (implies (nznp n)
                     (<= (etf n)
                         n)))
```

