datavtype queue_vt0ype_int_vtype(a: vt@ype+, n: int) =
  | {l, m: nat | (n == l + m) &&
     ((n == 0 && l == 0 && m == 0) ||
      (n >  0 && l > 0))}
     queue of (list_vt(a, l), list_vt(a, m))

stadef queue_vt = queue_vt0ype_int_vtype


fn {a:vt@ype}
length{n: nat}(!queue_vt(a, n)): int(n)

fn {a: vt@ype}
empty(): queue_vt(a, 0)

fn {a: vt@ype}
push{n: nat}(!queue_vt(a, n) >> queue_vt(a, n+1), a): void

fn {a: vt@ype}
pop{n: nat| n > 0}(&queue_vt(a, n) >> queue_vt(a, n-1)): a

fn {a: vt@ype}
pop_opt{n: nat}{b:bool| (n == 0 && b == false) || (n > 0 && b == true)}(&queue_vt(a, n) >> queue_vt(a, n-bool2int(b))): option_vt(a, b)