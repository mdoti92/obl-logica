# 0) Pre-condición y post-condición
- **Pre-condición**: Son condiciones que deben cumplirse antes de la ejecución de un método o un bucle para garantizar su correcto funcionamiento.
- **Post-condición**: Son condiciones que deben cumplirse después de la ejecución para verificar que el objetivo del método o bucle se haya alcanzado correctamente.


# 1) Invariantes de ciclos
Son condiciones que se tienen que mantener invariantes durante la ejecución en un bucle.

# 2) Desarrollo de los ciclos:
- **Inicialización**
- **Finalización**
- **Paso del ciclo**
    - Variante


# Métodos para pasar de pre y post condición a invariantes de cíclos

## Método 1:
*"Reemplazar constante(s) por variables(s)"*

### Ejemplo: Máximo de un array
a = array de enteros de 0 a |a|

Pre-condición:
- |a| > 0

Post-condición: 
- r == máx{ a[i] | 0 &le; i < |a| }
- &forall; i: 0 &le; i < |a| => a[i] &le; r && &exist; j: 0 &le; j < |a| && r == a[j]
- Escrito de otra forma:
    - b &equiv; &forall;i: 0 &le; < |a| => a[i] > 0

**Reemplazo de |a| por k**

- \(i_0\) &equiv; 0 <= k <= |a| &larr; **invariante de Cotas**
- \(i_1\) &equiv; b &equiv; &forall;i: 0 &le; i < k => a[i] > 0

**Inicialización**
- k,r := 0, a[0]

**Fin del cíclo**
- k == |a| || !b

**Paso del cíclo** (k != |a|)
1. **Actualizar \(r\):**
   \( k := k + 1 \) (Variante: |a|-k)

2. **Condición:**
   - Si \( r < a[k] \):
     ```plaintext
     r := a[k]
     ```
   - Si no:
     ```plaintext
     skip
     ```

## Método 2:
*Fortalecimiento de invariante*

### Ejemplo: Fibonacci
Pre: n &ge; 0
Post: f == fib(n)

Aplicamos "cambio de constante por variable"

\(i_0\) &equiv; 0 &le; k &le; n
\(i_1\) &equiv; f == fib(k)

Ini: k,f := 0, 1
Fin k == n
Paso: (k!=n)
Actualizar f: k:= k + 1

**Fortalecimiento del invariante**
- \(i_0\) &equiv; 0 &le; k &le; n
- \(i_1\) &equiv; f == fib(k)
- \(i_2\) &equiv; f' == fib(k+1)

Ini: k,f,f' := 0,1,1
Fin:= k == n

Paso: (k!=n)

Actualizar
k,f,f':= k+1, f', f+f'

## Método 3:
*Elegir condiciones*

### Ejemplo: Divisón entera con +, -

## Método 4: Tail Invariants

---


"Lo que yo quiero que ustedes experimentes es mas bien la cuestion de los invariantes y de la tecnica de metodos de desarrollo de los programas"