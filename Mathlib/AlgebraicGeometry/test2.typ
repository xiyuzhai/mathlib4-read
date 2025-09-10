== Field Spectra

```lean
instance {K} [Field K] : Unique Spec(K) := ...

lemma default_asIdeal {K} [Field K] : (default : Spec(K)).asIdeal = bot
```

*Natural Language:* The spectrum of a field is a single point, corresponding to the zero ideal (which is the unique maximal ideal in a field).