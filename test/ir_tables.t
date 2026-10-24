--dump-ir-tables は、KIR の組み込みの表(IRSpec 付録 A)を、付録の節の順に 1 行 1 項目で印字する。
印字するのは、KIR の書き出しと評価器が実際に使う表である。
行の頭の語は、付録 A の節を表す。

| 語 | 付録 A の節 | 欄 |
|---|---|---|
| `type` | A.1 組み込みの型 | 記号 |
| `class` | A.2 組み込みのクラス | 記号、メソッド(順) |
| `method` | A.3 組み込みのインスタンスのメソッド | クラス、型、メソッド、実装のプリミティブ(プリミティブで書かないものは `-`) |
| `value` | A.4 組み込みの値 | 記号 |
| `prim` | A.5 `extern "prim"` の実装名 | 実装名 |
| `c` | A.5 `extern "C"` の実装名 | 実装名 |

項目の数は、型 9、クラス 9、メソッド 44、値 12、プリミティブ 48、C の関数 5 である。

  $ diktor --dump-ir-tables | cut -d ' ' -f 1 | uniq -c | sed 's/^ *//'
  9 type
  9 class
  44 method
  12 value
  48 prim
  5 c
  $ diktor --dump-ir-tables
  type builtin/Boolean
  type builtin/Int32
  type builtin/Int64
  type builtin/Float64
  type builtin/String
  type builtin/Never
  type builtin/Ref
  type builtin/Array
  type builtin/MutableArray
  class builtin/Add add
  class builtin/Sub sub
  class builtin/Mul mul
  class builtin/Div div
  class builtin/Rem rem
  class builtin/Neg neg
  class builtin/Eq eq
  class builtin/Ord lt le gt ge
  class builtin/Show show
  method Add Int32 add __int32_add
  method Add Int64 add __int64_add
  method Add Float64 add __float64_add
  method Add String add __string_concat
  method Sub Int32 sub __int32_sub
  method Sub Int64 sub __int64_sub
  method Sub Float64 sub __float64_sub
  method Mul Int32 mul __int32_mul
  method Mul Int64 mul __int64_mul
  method Mul Float64 mul __float64_mul
  method Div Int32 div __int32_div
  method Div Int64 div __int64_div
  method Div Float64 div __float64_div
  method Rem Int32 rem __int32_rem
  method Rem Int64 rem __int64_rem
  method Neg Int32 neg __int32_neg
  method Neg Int64 neg __int64_neg
  method Neg Float64 neg __float64_neg
  method Eq Boolean eq -
  method Eq Int32 eq __int32_eq
  method Eq Int64 eq __int64_eq
  method Eq Float64 eq __float64_eq
  method Eq String eq __string_eq
  method Ord Int32 lt __int32_lt
  method Ord Int32 le __int32_le
  method Ord Int32 gt __int32_gt
  method Ord Int32 ge __int32_ge
  method Ord Int64 lt __int64_lt
  method Ord Int64 le __int64_le
  method Ord Int64 gt __int64_gt
  method Ord Int64 ge __int64_ge
  method Ord Float64 lt __float64_lt
  method Ord Float64 le __float64_le
  method Ord Float64 gt __float64_gt
  method Ord Float64 ge __float64_ge
  method Ord String lt __string_lt
  method Ord String le __string_le
  method Ord String gt __string_gt
  method Ord String ge __string_ge
  method Show Boolean show -
  method Show Int32 show __show_int32
  method Show Int64 show -
  method Show Float64 show -
  method Show String show -
  value builtin/Ref.new
  value builtin/Ref.get
  value builtin/Ref.set
  value builtin/Array.length
  value builtin/Array.get
  value builtin/Array.each
  value builtin/MutableArray.new
  value builtin/MutableArray.length
  value builtin/MutableArray.get
  value builtin/MutableArray.set
  value builtin/MutableArray.freeze
  value builtin/pinned
  prim __int32_add
  prim __int32_sub
  prim __int32_mul
  prim __int32_div
  prim __int32_rem
  prim __int32_neg
  prim __int32_eq
  prim __int32_lt
  prim __int32_le
  prim __int32_gt
  prim __int32_ge
  prim __int64_add
  prim __int64_sub
  prim __int64_mul
  prim __int64_div
  prim __int64_rem
  prim __int64_neg
  prim __int64_eq
  prim __int64_lt
  prim __int64_le
  prim __int64_gt
  prim __int64_ge
  prim __float64_add
  prim __float64_sub
  prim __float64_mul
  prim __float64_div
  prim __float64_neg
  prim __float64_eq
  prim __float64_lt
  prim __float64_le
  prim __float64_gt
  prim __float64_ge
  prim __string_concat
  prim __string_eq
  prim __string_lt
  prim __string_le
  prim __string_gt
  prim __string_ge
  prim __string_length
  prim __string_sub
  prim __i32_to_i64
  prim __i32_to_f64
  prim __i64_to_i32
  prim __i64_to_f64
  prim __f64_to_i32
  prim __f64_to_i64
  prim __show_int32
  prim __panic
  c sin
  c cos
  c sqrt
  c exp
  c log

入力のファイルは書けず、KIR を書く旗や実行する旗とも併せられない(64)。

  $ printf 'let x = 1\n' > one.kel
  $ diktor --dump-ir-tables one.kel 2>&1 | head -1; diktor --dump-ir-tables one.kel > /dev/null 2>&1; echo "exit: $?"
  diktor: --dump-ir-tables takes no input files
  exit: 64
  $ diktor --dump-ir-tables --via-ir 2>&1 | head -1; diktor --dump-ir-tables --via-ir > /dev/null 2>&1; echo "exit: $?"
  diktor: --dump-ir-tables cannot be combined with --emit-ir, --emit-ir-text, --run-ir or --via-ir
  exit: 64
  $ diktor --dump-ir-tables --emit-ir x.kir > /dev/null 2>&1; echo "exit: $?"; test -e x.kir || echo "no file"
  exit: 64
  no file
