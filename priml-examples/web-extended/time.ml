open Unix
let tm_sec tm = tm.tm_sec
let tm_min tm = tm.tm_min
let tm_hour tm = tm.tm_hour
let tm_mday tm = tm.tm_mday
let tm_wday tm = tm.tm_wday
let tm_mon tm = tm.tm_mon
let tm_year tm = tm.tm_year

let tsminus t1 t2 = t1 -. t2
let tsless t1 t2 = t1 < (float_of_int t2)

let print s = Printf.printf "%s" s
