# CakeML-based proof checker

This contains some temporary files sketching out what the CakeML-based backing proof checker for ImpCheck would look like.

- `rup.cml` : this is a temporary sketch file (will be replaced by verified code)
- `rup.S` : this is the compiled assembly (currently generated from `rup.cml` by a copy of the CakeML compiler)

`cmake` is currently configured to build with:

```
./cake --main_return=true < rup.cml > rup.S
```

The generated `rup.S` is linked into `impcheck_check`.
