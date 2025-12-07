# Cobb_Totem

## Setup

If you get an error like `unknown module prefix 'Aesop'` when running `lake env lean --stdin`, try:

```bash
lake update
lake build aesop
lake build hammer
```