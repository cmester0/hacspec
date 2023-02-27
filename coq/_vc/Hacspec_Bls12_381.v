(** This file was automatically generated using Hacspec **)
Set Warnings "-notation-overridden,-ambiguous-paths".
Require Import Hacspec_Lib MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.

From QuickChick Require Import QuickChick.
Require Import QuickChickLib.
Require Import Hacspec_Lib.
Export Hacspec_Lib.

Definition fp_canvas_t := nseq (int8) (48).
Definition fp_t :=
  nat_mod 0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab.
Instance show_fp_t : Show (fp_t) := Build_Show (fp_t) (fun x => show (GZnZ.val _ x)).
Definition g_fp_t : G (fp_t) := @bindGen Z (fp_t) (arbitrary) (fun x => returnGen (@Z_in_nat_mod _ x)).
Instance gen_fp_t : Gen (fp_t) := Build_Gen fp_t g_fp_t.


Definition serialized_fp_t := nseq (uint8) (usize 48).

Definition array_fp_t := nseq (uint64) (usize 6).

Definition scalar_canvas_t := nseq (int8) (32).
Definition scalar_t :=
  nat_mod 0x8000000000000000000000000000000000000000000000000000000000000000.
Instance show_scalar_t : Show (scalar_t) := Build_Show (scalar_t) (fun x => show (GZnZ.val _ x)).
Definition g_scalar_t : G (scalar_t) := @bindGen Z (scalar_t) (arbitrary) (fun x => returnGen (@Z_in_nat_mod _ x)).
Instance gen_scalar_t : Gen (scalar_t) := Build_Gen scalar_t g_scalar_t.


Notation "'g1_t'" := ((fp_t '× fp_t '× bool)) : hacspec_scope.
Instance show_g1_t : Show (g1_t) :=
Build_Show g1_t (fun x =>
  let (x, x0) := x in
  let (x, x1) := x in
  (
    ("(") ++ ((show x) ++ ((",") ++ ((show x0) ++ ((",") ++ ((show x1) ++ (")"))))))))%string.
Definition g_g1_t : G (g1_t) :=
bindGen arbitrary (fun x0 : fp_t =>
  bindGen arbitrary (fun x1 : fp_t =>
  bindGen arbitrary (fun x2 : bool =>
  returnGen (x0,x1,x2)))).
Instance gen_g1_t : Gen (g1_t) := Build_Gen g1_t g_g1_t.


Notation "'fp2_t'" := ((fp_t '× fp_t)) : hacspec_scope.
Instance show_fp2_t : Show (fp2_t) :=
Build_Show fp2_t (fun x =>
  let (x, x0) := x in
  (("(") ++ ((show x) ++ ((",") ++ ((show x0) ++ (")"))))))%string.
Definition g_fp2_t : G (fp2_t) :=
bindGen arbitrary (fun x0 : fp_t =>
  bindGen arbitrary (fun x1 : fp_t =>
  returnGen (x0,x1))).
Instance gen_fp2_t : Gen (fp2_t) := Build_Gen fp2_t g_fp2_t.


Notation "'g2_t'" := ((fp2_t '× fp2_t '× bool)) : hacspec_scope.
Instance show_g2_t : Show (g2_t) :=
Build_Show g2_t (fun x =>
  let (x, x0) := x in
  let (x, x1) := x in
  (
    ("(") ++ ((show x) ++ ((",") ++ ((show x0) ++ ((",") ++ ((show x1) ++ (")"))))))))%string.
Definition g_g2_t : G (g2_t) :=
bindGen arbitrary (fun x0 : fp2_t =>
  bindGen arbitrary (fun x1 : fp2_t =>
  bindGen arbitrary (fun x2 : bool =>
  returnGen (x0,x1,x2)))).
Instance gen_g2_t : Gen (g2_t) := Build_Gen g2_t g_g2_t.


Notation "'fp6_t'" := ((fp2_t '× fp2_t '× fp2_t)) : hacspec_scope.
Instance show_fp6_t : Show (fp6_t) :=
Build_Show fp6_t (fun x =>
  let (x, x0) := x in
  let (x, x1) := x in
  (
    ("(") ++ ((show x) ++ ((",") ++ ((show x0) ++ ((",") ++ ((show x1) ++ (")"))))))))%string.
Definition g_fp6_t : G (fp6_t) :=
bindGen arbitrary (fun x0 : fp2_t =>
  bindGen arbitrary (fun x1 : fp2_t =>
  bindGen arbitrary (fun x2 : fp2_t =>
  returnGen (x0,x1,x2)))).
Instance gen_fp6_t : Gen (fp6_t) := Build_Gen fp6_t g_fp6_t.


Notation "'fp12_t'" := ((fp6_t '× fp6_t)) : hacspec_scope.
Instance show_fp12_t : Show (fp12_t) :=
Build_Show fp12_t (fun x =>
  let (x, x0) := x in
  (("(") ++ ((show x) ++ ((",") ++ ((show x0) ++ (")"))))))%string.
Definition g_fp12_t : G (fp12_t) :=
bindGen arbitrary (fun x0 : fp6_t =>
  bindGen arbitrary (fun x1 : fp6_t =>
  returnGen (x0,x1))).
Instance gen_fp12_t : Gen (fp12_t) := Build_Gen fp12_t g_fp12_t.


Definition fp2fromfp (n_1255 : fp_t)  : fp2_t :=
  (n_1255, nat_mod_zero ).


Definition fp2zero   : fp2_t :=
  fp2fromfp (nat_mod_zero ).


Definition fp2neg (n_1256 : fp2_t)  : fp2_t :=
  let '(n1_1257, n2_1258) :=
    n_1256 in 
  ((nat_mod_zero ) -% (n1_1257), (nat_mod_zero ) -% (n2_1258)).


Definition fp2add (n_1259 : fp2_t) (m_1260 : fp2_t)  : fp2_t :=
  let '(n1_1261, n2_1262) :=
    n_1259 in 
  let '(m1_1263, m2_1264) :=
    m_1260 in 
  ((n1_1261) +% (m1_1263), (n2_1262) +% (m2_1264)).


Definition fp2sub (n_1265 : fp2_t) (m_1266 : fp2_t)  : fp2_t :=
  fp2add (n_1265) (fp2neg (m_1266)).


Definition fp2mul (n_1267 : fp2_t) (m_1268 : fp2_t)  : fp2_t :=
  let '(n1_1269, n2_1270) :=
    n_1267 in 
  let '(m1_1271, m2_1272) :=
    m_1268 in 
  let x1_1273 : fp_t :=
    ((n1_1269) *% (m1_1271)) -% ((n2_1270) *% (m2_1272)) in 
  let x2_1274 : fp_t :=
    ((n1_1269) *% (m2_1272)) +% ((n2_1270) *% (m1_1271)) in 
  (x1_1273, x2_1274).


Definition fp2inv (n_1275 : fp2_t)  : fp2_t :=
  let '(n1_1276, n2_1277) :=
    n_1275 in 
  let t0_1278 : fp_t :=
    ((n1_1276) *% (n1_1276)) +% ((n2_1277) *% (n2_1277)) in 
  let t1_1279 : fp_t :=
    nat_mod_inv (t0_1278) in 
  let x1_1280 : fp_t :=
    (n1_1276) *% (t1_1279) in 
  let x2_1281 : fp_t :=
    (nat_mod_zero ) -% ((n2_1277) *% (t1_1279)) in 
  (x1_1280, x2_1281).


Definition fp2conjugate (n_1282 : fp2_t)  : fp2_t :=
  let '(n1_1283, n2_1284) :=
    n_1282 in 
  (n1_1283, (nat_mod_zero ) -% (n2_1284)).


Definition fp6fromfp2 (n_1285 : fp2_t)  : fp6_t :=
  (n_1285, fp2zero , fp2zero ).


Definition fp6zero   : fp6_t :=
  fp6fromfp2 (fp2zero ).


Definition fp6neg (n_1286 : fp6_t)  : fp6_t :=
  let '(n1_1287, n2_1288, n3_1289) :=
    n_1286 in 
  (
    fp2sub (fp2zero ) (n1_1287),
    fp2sub (fp2zero ) (n2_1288),
    fp2sub (fp2zero ) (n3_1289)
  ).


Definition fp6add (n_1290 : fp6_t) (m_1291 : fp6_t)  : fp6_t :=
  let '(n1_1292, n2_1293, n3_1294) :=
    n_1290 in 
  let '(m1_1295, m2_1296, m3_1297) :=
    m_1291 in 
  (
    fp2add (n1_1292) (m1_1295),
    fp2add (n2_1293) (m2_1296),
    fp2add (n3_1294) (m3_1297)
  ).


Definition fp6sub (n_1298 : fp6_t) (m_1299 : fp6_t)  : fp6_t :=
  fp6add (n_1298) (fp6neg (m_1299)).


Definition fp6mul (n_1300 : fp6_t) (m_1301 : fp6_t)  : fp6_t :=
  let '(n1_1302, n2_1303, n3_1304) :=
    n_1300 in 
  let '(m1_1305, m2_1306, m3_1307) :=
    m_1301 in 
  let eps_1308 : (fp_t '× fp_t) :=
    (nat_mod_one , nat_mod_one ) in 
  let t1_1309 : (fp_t '× fp_t) :=
    fp2mul (n1_1302) (m1_1305) in 
  let t2_1310 : (fp_t '× fp_t) :=
    fp2mul (n2_1303) (m2_1306) in 
  let t3_1311 : (fp_t '× fp_t) :=
    fp2mul (n3_1304) (m3_1307) in 
  let t4_1312 : (fp_t '× fp_t) :=
    fp2mul (fp2add (n2_1303) (n3_1304)) (fp2add (m2_1306) (m3_1307)) in 
  let t5_1313 : (fp_t '× fp_t) :=
    fp2sub (fp2sub (t4_1312) (t2_1310)) (t3_1311) in 
  let x_1314 : (fp_t '× fp_t) :=
    fp2add (fp2mul (t5_1313) (eps_1308)) (t1_1309) in 
  let t4_1315 : (fp_t '× fp_t) :=
    fp2mul (fp2add (n1_1302) (n2_1303)) (fp2add (m1_1305) (m2_1306)) in 
  let t5_1316 : (fp_t '× fp_t) :=
    fp2sub (fp2sub (t4_1315) (t1_1309)) (t2_1310) in 
  let y_1317 : (fp_t '× fp_t) :=
    fp2add (t5_1316) (fp2mul (eps_1308) (t3_1311)) in 
  let t4_1318 : (fp_t '× fp_t) :=
    fp2mul (fp2add (n1_1302) (n3_1304)) (fp2add (m1_1305) (m3_1307)) in 
  let t5_1319 : (fp_t '× fp_t) :=
    fp2sub (fp2sub (t4_1318) (t1_1309)) (t3_1311) in 
  let z_1320 : (fp_t '× fp_t) :=
    fp2add (t5_1319) (t2_1310) in 
  (x_1314, y_1317, z_1320).


Definition fp6inv (n_1321 : fp6_t)  : fp6_t :=
  let '(n1_1322, n2_1323, n3_1324) :=
    n_1321 in 
  let eps_1325 : (fp_t '× fp_t) :=
    (nat_mod_one , nat_mod_one ) in 
  let t1_1326 : (fp_t '× fp_t) :=
    fp2mul (n1_1322) (n1_1322) in 
  let t2_1327 : (fp_t '× fp_t) :=
    fp2mul (n2_1323) (n2_1323) in 
  let t3_1328 : (fp_t '× fp_t) :=
    fp2mul (n3_1324) (n3_1324) in 
  let t4_1329 : (fp_t '× fp_t) :=
    fp2mul (n1_1322) (n2_1323) in 
  let t5_1330 : (fp_t '× fp_t) :=
    fp2mul (n1_1322) (n3_1324) in 
  let t6_1331 : (fp_t '× fp_t) :=
    fp2mul (n2_1323) (n3_1324) in 
  let x0_1332 : (fp_t '× fp_t) :=
    fp2sub (t1_1326) (fp2mul (eps_1325) (t6_1331)) in 
  let y0_1333 : (fp_t '× fp_t) :=
    fp2sub (fp2mul (eps_1325) (t3_1328)) (t4_1329) in 
  let z0_1334 : (fp_t '× fp_t) :=
    fp2sub (t2_1327) (t5_1330) in 
  let t0_1335 : (fp_t '× fp_t) :=
    fp2mul (n1_1322) (x0_1332) in 
  let t0_1336 : (fp_t '× fp_t) :=
    fp2add (t0_1335) (fp2mul (eps_1325) (fp2mul (n3_1324) (y0_1333))) in 
  let t0_1337 : (fp_t '× fp_t) :=
    fp2add (t0_1336) (fp2mul (eps_1325) (fp2mul (n2_1323) (z0_1334))) in 
  let t0_1338 : (fp_t '× fp_t) :=
    fp2inv (t0_1337) in 
  let x_1339 : (fp_t '× fp_t) :=
    fp2mul (x0_1332) (t0_1338) in 
  let y_1340 : (fp_t '× fp_t) :=
    fp2mul (y0_1333) (t0_1338) in 
  let z_1341 : (fp_t '× fp_t) :=
    fp2mul (z0_1334) (t0_1338) in 
  (x_1339, y_1340, z_1341).


Definition fp12fromfp6 (n_1342 : fp6_t)  : fp12_t :=
  (n_1342, fp6zero ).


Definition fp12neg (n_1343 : fp12_t)  : fp12_t :=
  let '(n1_1344, n2_1345) :=
    n_1343 in 
  (fp6sub (fp6zero ) (n1_1344), fp6sub (fp6zero ) (n2_1345)).


Definition fp12add (n_1346 : fp12_t) (m_1347 : fp12_t)  : fp12_t :=
  let '(n1_1348, n2_1349) :=
    n_1346 in 
  let '(m1_1350, m2_1351) :=
    m_1347 in 
  (fp6add (n1_1348) (m1_1350), fp6add (n2_1349) (m2_1351)).


Definition fp12sub (n_1352 : fp12_t) (m_1353 : fp12_t)  : fp12_t :=
  fp12add (n_1352) (fp12neg (m_1353)).


Definition fp12mul (n_1354 : fp12_t) (m_1355 : fp12_t)  : fp12_t :=
  let '(n1_1356, n2_1357) :=
    n_1354 in 
  let '(m1_1358, m2_1359) :=
    m_1355 in 
  let gamma_1360 : (fp2_t '× fp2_t '× fp2_t) :=
    (fp2zero , fp2fromfp (nat_mod_one ), fp2zero ) in 
  let t1_1361 : (fp2_t '× fp2_t '× fp2_t) :=
    fp6mul (n1_1356) (m1_1358) in 
  let t2_1362 : (fp2_t '× fp2_t '× fp2_t) :=
    fp6mul (n2_1357) (m2_1359) in 
  let x_1363 : (fp2_t '× fp2_t '× fp2_t) :=
    fp6add (t1_1361) (fp6mul (t2_1362) (gamma_1360)) in 
  let y_1364 : (fp2_t '× fp2_t '× fp2_t) :=
    fp6mul (fp6add (n1_1356) (n2_1357)) (fp6add (m1_1358) (m2_1359)) in 
  let y_1365 : (fp2_t '× fp2_t '× fp2_t) :=
    fp6sub (fp6sub (y_1364) (t1_1361)) (t2_1362) in 
  (x_1363, y_1365).


Definition fp12inv (n_1366 : fp12_t)  : fp12_t :=
  let '(n1_1367, n2_1368) :=
    n_1366 in 
  let gamma_1369 : (fp2_t '× fp2_t '× fp2_t) :=
    (fp2zero , fp2fromfp (nat_mod_one ), fp2zero ) in 
  let t1_1370 : (fp2_t '× fp2_t '× fp2_t) :=
    fp6mul (n1_1367) (n1_1367) in 
  let t2_1371 : (fp2_t '× fp2_t '× fp2_t) :=
    fp6mul (n2_1368) (n2_1368) in 
  let t1_1372 : (fp2_t '× fp2_t '× fp2_t) :=
    fp6sub (t1_1370) (fp6mul (gamma_1369) (t2_1371)) in 
  let t2_1373 : (fp2_t '× fp2_t '× fp2_t) :=
    fp6inv (t1_1372) in 
  let x_1374 : (fp2_t '× fp2_t '× fp2_t) :=
    fp6mul (n1_1367) (t2_1373) in 
  let y_1375 : (fp2_t '× fp2_t '× fp2_t) :=
    fp6neg (fp6mul (n2_1368) (t2_1373)) in 
  (x_1374, y_1375).


Definition fp12exp (n_1376 : fp12_t) (k_1377 : scalar_t)  : fp12_t :=
  let c_1378 : (fp6_t '× fp6_t) :=
    fp12fromfp6 (fp6fromfp2 (fp2fromfp (nat_mod_one ))) in 
  let c_1378 :=
    foldi (usize 0) (usize 256) (fun i_1379 c_1378 =>
      let c_1378 :=
        fp12mul (c_1378) (c_1378) in 
      let '(c_1378) :=
        if nat_mod_bit (k_1377) ((usize 255) - (i_1379)):bool then (
          let c_1378 :=
            fp12mul (c_1378) (n_1376) in 
          (c_1378)) else ((c_1378)) in 
      (c_1378))
    c_1378 in 
  c_1378.


Definition fp12conjugate (n_1380 : fp12_t)  : fp12_t :=
  let '(n1_1381, n2_1382) :=
    n_1380 in 
  (n1_1381, fp6neg (n2_1382)).


Definition fp12zero   : fp12_t :=
  fp12fromfp6 (fp6zero ).


Definition g1add_a (p_1383 : g1_t) (q_1384 : g1_t)  : g1_t :=
  let '(x1_1385, y1_1386, _) :=
    p_1383 in 
  let '(x2_1387, y2_1388, _) :=
    q_1384 in 
  let x_diff_1389 : fp_t :=
    (x2_1387) -% (x1_1385) in 
  let y_diff_1390 : fp_t :=
    (y2_1388) -% (y1_1386) in 
  let xovery_1391 : fp_t :=
    (y_diff_1390) *% (nat_mod_inv (x_diff_1389)) in 
  let x3_1392 : fp_t :=
    ((nat_mod_exp (xovery_1391) (@repr WORDSIZE32 (2))) -% (x1_1385)) -% (
      x2_1387) in 
  let y3_1393 : fp_t :=
    ((xovery_1391) *% ((x1_1385) -% (x3_1392))) -% (y1_1386) in 
  (x3_1392, y3_1393, false).


Definition g1double_a (p_1394 : g1_t)  : g1_t :=
  let '(x1_1395, y1_1396, _) :=
    p_1394 in 
  let x12_1397 : fp_t :=
    nat_mod_exp (x1_1395) (@repr WORDSIZE32 (2)) in 
  let xovery_1398 : fp_t :=
    ((nat_mod_from_literal (
          0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab) (
          @repr WORDSIZE128 3) : fp_t) *% (x12_1397)) *% (nat_mod_inv ((
          nat_mod_two ) *% (y1_1396))) in 
  let x3_1399 : fp_t :=
    (nat_mod_exp (xovery_1398) (@repr WORDSIZE32 (2))) -% ((nat_mod_two ) *% (
        x1_1395)) in 
  let y3_1400 : fp_t :=
    ((xovery_1398) *% ((x1_1395) -% (x3_1399))) -% (y1_1396) in 
  (x3_1399, y3_1400, false).


Definition g1double (p_1401 : g1_t)  : g1_t :=
  let '(x1_1402, y1_1403, inf1_1404) :=
    p_1401 in 
  (if (((y1_1403) !=.? (nat_mod_zero )) && (negb (inf1_1404))):bool then (
      g1double_a (p_1401)) else ((nat_mod_zero , nat_mod_zero , true))).


Definition g1add (p_1405 : g1_t) (q_1406 : g1_t)  : g1_t :=
  let '(x1_1407, y1_1408, inf1_1409) :=
    p_1405 in 
  let '(x2_1410, y2_1411, inf2_1412) :=
    q_1406 in 
  (if (inf1_1409):bool then (q_1406) else ((if (inf2_1412):bool then (
          p_1405) else ((if ((p_1405) =.? (q_1406)):bool then (g1double (
                p_1405)) else ((if (negb (((x1_1407) =.? (x2_1410)) && ((
                        y1_1408) =.? ((nat_mod_zero ) -% (
                          y2_1411))))):bool then (g1add_a (p_1405) (
                    q_1406)) else ((nat_mod_zero , nat_mod_zero , true))))))))).


Definition g1mul (m_1413 : scalar_t) (p_1414 : g1_t)  : g1_t :=
  let t_1415 : (fp_t '× fp_t '× bool) :=
    (nat_mod_zero , nat_mod_zero , true) in 
  let t_1415 :=
    foldi (usize 0) (usize 256) (fun i_1416 t_1415 =>
      let t_1415 :=
        g1double (t_1415) in 
      let '(t_1415) :=
        if nat_mod_bit (m_1413) ((usize 255) - (i_1416)):bool then (
          let t_1415 :=
            g1add (t_1415) (p_1414) in 
          (t_1415)) else ((t_1415)) in 
      (t_1415))
    t_1415 in 
  t_1415.


Definition g1neg (p_1417 : g1_t)  : g1_t :=
  let '(x_1418, y_1419, inf_1420) :=
    p_1417 in 
  (x_1418, (nat_mod_zero ) -% (y_1419), inf_1420).


Definition g2add_a (p_1421 : g2_t) (q_1422 : g2_t)  : g2_t :=
  let '(x1_1423, y1_1424, _) :=
    p_1421 in 
  let '(x2_1425, y2_1426, _) :=
    q_1422 in 
  let x_diff_1427 : (fp_t '× fp_t) :=
    fp2sub (x2_1425) (x1_1423) in 
  let y_diff_1428 : (fp_t '× fp_t) :=
    fp2sub (y2_1426) (y1_1424) in 
  let xovery_1429 : (fp_t '× fp_t) :=
    fp2mul (y_diff_1428) (fp2inv (x_diff_1427)) in 
  let t1_1430 : (fp_t '× fp_t) :=
    fp2mul (xovery_1429) (xovery_1429) in 
  let t2_1431 : (fp_t '× fp_t) :=
    fp2sub (t1_1430) (x1_1423) in 
  let x3_1432 : (fp_t '× fp_t) :=
    fp2sub (t2_1431) (x2_1425) in 
  let t1_1433 : (fp_t '× fp_t) :=
    fp2sub (x1_1423) (x3_1432) in 
  let t2_1434 : (fp_t '× fp_t) :=
    fp2mul (xovery_1429) (t1_1433) in 
  let y3_1435 : (fp_t '× fp_t) :=
    fp2sub (t2_1434) (y1_1424) in 
  (x3_1432, y3_1435, false).


Definition g2double_a (p_1436 : g2_t)  : g2_t :=
  let '(x1_1437, y1_1438, _) :=
    p_1436 in 
  let x12_1439 : (fp_t '× fp_t) :=
    fp2mul (x1_1437) (x1_1437) in 
  let t1_1440 : (fp_t '× fp_t) :=
    fp2mul (fp2fromfp (nat_mod_from_literal (
          0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab) (
          @repr WORDSIZE128 3) : fp_t)) (x12_1439) in 
  let t2_1441 : (fp_t '× fp_t) :=
    fp2inv (fp2mul (fp2fromfp (nat_mod_two )) (y1_1438)) in 
  let xovery_1442 : (fp_t '× fp_t) :=
    fp2mul (t1_1440) (t2_1441) in 
  let t1_1443 : (fp_t '× fp_t) :=
    fp2mul (xovery_1442) (xovery_1442) in 
  let t2_1444 : (fp_t '× fp_t) :=
    fp2mul (fp2fromfp (nat_mod_two )) (x1_1437) in 
  let x3_1445 : (fp_t '× fp_t) :=
    fp2sub (t1_1443) (t2_1444) in 
  let t1_1446 : (fp_t '× fp_t) :=
    fp2sub (x1_1437) (x3_1445) in 
  let t2_1447 : (fp_t '× fp_t) :=
    fp2mul (xovery_1442) (t1_1446) in 
  let y3_1448 : (fp_t '× fp_t) :=
    fp2sub (t2_1447) (y1_1438) in 
  (x3_1445, y3_1448, false).


Definition g2double (p_1449 : g2_t)  : g2_t :=
  let '(x1_1450, y1_1451, inf1_1452) :=
    p_1449 in 
  (if (((y1_1451) !=.? (fp2zero )) && (negb (inf1_1452))):bool then (
      g2double_a (p_1449)) else ((fp2zero , fp2zero , true))).


Definition g2add (p_1453 : g2_t) (q_1454 : g2_t)  : g2_t :=
  let '(x1_1455, y1_1456, inf1_1457) :=
    p_1453 in 
  let '(x2_1458, y2_1459, inf2_1460) :=
    q_1454 in 
  (if (inf1_1457):bool then (q_1454) else ((if (inf2_1460):bool then (
          p_1453) else ((if ((p_1453) =.? (q_1454)):bool then (g2double (
                p_1453)) else ((if (negb (((x1_1455) =.? (x2_1458)) && ((
                        y1_1456) =.? (fp2neg (y2_1459))))):bool then (g2add_a (
                    p_1453) (q_1454)) else ((fp2zero , fp2zero , true))))))))).


Definition g2mul (m_1461 : scalar_t) (p_1462 : g2_t)  : g2_t :=
  let t_1463 : (fp2_t '× fp2_t '× bool) :=
    (fp2zero , fp2zero , true) in 
  let t_1463 :=
    foldi (usize 0) (usize 256) (fun i_1464 t_1463 =>
      let t_1463 :=
        g2double (t_1463) in 
      let '(t_1463) :=
        if nat_mod_bit (m_1461) ((usize 255) - (i_1464)):bool then (
          let t_1463 :=
            g2add (t_1463) (p_1462) in 
          (t_1463)) else ((t_1463)) in 
      (t_1463))
    t_1463 in 
  t_1463.


Definition g2neg (p_1465 : g2_t)  : g2_t :=
  let '(x_1466, y_1467, inf_1468) :=
    p_1465 in 
  (x_1466, fp2neg (y_1467), inf_1468).


Definition twist (p_1469 : g1_t)  : (fp12_t '× fp12_t) :=
  let '(p0_1470, p1_1471, _) :=
    p_1469 in 
  let x_1472 : ((fp2_t '× fp2_t '× fp2_t) '× fp6_t) :=
    ((fp2zero , fp2fromfp (p0_1470), fp2zero ), fp6zero ) in 
  let y_1473 : (fp6_t '× (fp2_t '× fp2_t '× fp2_t)) :=
    (fp6zero , (fp2zero , fp2fromfp (p1_1471), fp2zero )) in 
  (x_1472, y_1473).


Definition line_double_p (r_1474 : g2_t) (p_1475 : g1_t)  : fp12_t :=
  let '(r0_1476, r1_1477, _) :=
    r_1474 in 
  let a_1478 : (fp_t '× fp_t) :=
    fp2mul (fp2fromfp (nat_mod_from_literal (
          0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab) (
          @repr WORDSIZE128 3) : fp_t)) (fp2mul (r0_1476) (r0_1476)) in 
  let a_1479 : (fp_t '× fp_t) :=
    fp2mul (a_1478) (fp2inv (fp2mul (fp2fromfp (nat_mod_two )) (r1_1477))) in 
  let b_1480 : (fp_t '× fp_t) :=
    fp2sub (r1_1477) (fp2mul (a_1479) (r0_1476)) in 
  let a_1481 : (fp6_t '× fp6_t) :=
    fp12fromfp6 (fp6fromfp2 (a_1479)) in 
  let b_1482 : (fp6_t '× fp6_t) :=
    fp12fromfp6 (fp6fromfp2 (b_1480)) in 
  let '(x_1483, y_1484) :=
    twist (p_1475) in 
  fp12neg (fp12sub (fp12sub (y_1484) (fp12mul (a_1481) (x_1483))) (b_1482)).


Definition line_add_p
  (r_1485 : g2_t)
  (q_1486 : g2_t)
  (p_1487 : g1_t)
  
  : fp12_t :=
  let '(r0_1488, r1_1489, _) :=
    r_1485 in 
  let '(q0_1490, q1_1491, _) :=
    q_1486 in 
  let a_1492 : (fp_t '× fp_t) :=
    fp2mul (fp2sub (q1_1491) (r1_1489)) (fp2inv (fp2sub (q0_1490) (
          r0_1488))) in 
  let b_1493 : (fp_t '× fp_t) :=
    fp2sub (r1_1489) (fp2mul (a_1492) (r0_1488)) in 
  let a_1494 : (fp6_t '× fp6_t) :=
    fp12fromfp6 (fp6fromfp2 (a_1492)) in 
  let b_1495 : (fp6_t '× fp6_t) :=
    fp12fromfp6 (fp6fromfp2 (b_1493)) in 
  let '(x_1496, y_1497) :=
    twist (p_1487) in 
  fp12neg (fp12sub (fp12sub (y_1497) (fp12mul (a_1494) (x_1496))) (b_1495)).


Definition frobenius (f_1498 : fp12_t)  : fp12_t :=
  let '((g0_1499, g1_1500, g2_1501), (h0_1502, h1_1503, h2_1504)) :=
    f_1498 in 
  let t1_1505 : (fp_t '× fp_t) :=
    fp2conjugate (g0_1499) in 
  let t2_1506 : (fp_t '× fp_t) :=
    fp2conjugate (h0_1502) in 
  let t3_1507 : (fp_t '× fp_t) :=
    fp2conjugate (g1_1500) in 
  let t4_1508 : (fp_t '× fp_t) :=
    fp2conjugate (h1_1503) in 
  let t5_1509 : (fp_t '× fp_t) :=
    fp2conjugate (g2_1501) in 
  let t6_1510 : (fp_t '× fp_t) :=
    fp2conjugate (h2_1504) in 
  let c1_1511 : array_fp_t :=
    array_from_list uint64 (let l :=
        [
          secret (@repr WORDSIZE64 10162220747404304312) : int64;
          secret (@repr WORDSIZE64 17761815663483519293) : int64;
          secret (@repr WORDSIZE64 8873291758750579140) : int64;
          secret (@repr WORDSIZE64 1141103941765652303) : int64;
          secret (@repr WORDSIZE64 13993175198059990303) : int64;
          secret (@repr WORDSIZE64 1802798568193066599) : int64
        ] in  l) in 
  let c1_1512 : seq uint8 :=
    array_to_le_bytes (c1_1511) in 
  let c1_1513 : fp_t :=
    nat_mod_from_byte_seq_le (c1_1512) : fp_t in 
  let c2_1514 : array_fp_t :=
    array_from_list uint64 (let l :=
        [
          secret (@repr WORDSIZE64 3240210268673559283) : int64;
          secret (@repr WORDSIZE64 2895069921743240898) : int64;
          secret (@repr WORDSIZE64 17009126888523054175) : int64;
          secret (@repr WORDSIZE64 6098234018649060207) : int64;
          secret (@repr WORDSIZE64 9865672654120263608) : int64;
          secret (@repr WORDSIZE64 71000049454473266) : int64
        ] in  l) in 
  let c2_1515 : seq uint8 :=
    array_to_le_bytes (c2_1514) in 
  let c2_1516 : fp_t :=
    nat_mod_from_byte_seq_le (c2_1515) : fp_t in 
  let gamma11_1517 : (fp_t '× fp_t) :=
    (c1_1513, c2_1516) in 
  let gamma12_1518 : (fp_t '× fp_t) :=
    fp2mul (gamma11_1517) (gamma11_1517) in 
  let gamma13_1519 : (fp_t '× fp_t) :=
    fp2mul (gamma12_1518) (gamma11_1517) in 
  let gamma14_1520 : (fp_t '× fp_t) :=
    fp2mul (gamma13_1519) (gamma11_1517) in 
  let gamma15_1521 : (fp_t '× fp_t) :=
    fp2mul (gamma14_1520) (gamma11_1517) in 
  let t2_1522 : (fp_t '× fp_t) :=
    fp2mul (t2_1506) (gamma11_1517) in 
  let t3_1523 : (fp_t '× fp_t) :=
    fp2mul (t3_1507) (gamma12_1518) in 
  let t4_1524 : (fp_t '× fp_t) :=
    fp2mul (t4_1508) (gamma13_1519) in 
  let t5_1525 : (fp_t '× fp_t) :=
    fp2mul (t5_1509) (gamma14_1520) in 
  let t6_1526 : (fp_t '× fp_t) :=
    fp2mul (t6_1510) (gamma15_1521) in 
  ((t1_1505, t3_1523, t5_1525), (t2_1522, t4_1524, t6_1526)).


Definition final_exponentiation (f_1527 : fp12_t)  : fp12_t :=
  let fp6_1528 : (fp6_t '× fp6_t) :=
    fp12conjugate (f_1527) in 
  let finv_1529 : (fp6_t '× fp6_t) :=
    fp12inv (f_1527) in 
  let fp6_1_1530 : (fp6_t '× fp6_t) :=
    fp12mul (fp6_1528) (finv_1529) in 
  let fp8_1531 : (fp6_t '× fp6_t) :=
    frobenius (frobenius (fp6_1_1530)) in 
  let f_1532 : (fp6_t '× fp6_t) :=
    fp12mul (fp8_1531) (fp6_1_1530) in 
  let u_1533 : scalar_t :=
    nat_mod_from_literal (
      0x8000000000000000000000000000000000000000000000000000000000000000) (
      @repr WORDSIZE128 15132376222941642752) : scalar_t in 
  let u_half_1534 : scalar_t :=
    nat_mod_from_literal (
      0x8000000000000000000000000000000000000000000000000000000000000000) (
      @repr WORDSIZE128 7566188111470821376) : scalar_t in 
  let t0_1535 : (fp6_t '× fp6_t) :=
    fp12mul (f_1532) (f_1532) in 
  let t1_1536 : (fp6_t '× fp6_t) :=
    fp12exp (t0_1535) (u_1533) in 
  let t1_1537 : (fp6_t '× fp6_t) :=
    fp12conjugate (t1_1536) in 
  let t2_1538 : (fp6_t '× fp6_t) :=
    fp12exp (t1_1537) (u_half_1534) in 
  let t2_1539 : (fp6_t '× fp6_t) :=
    fp12conjugate (t2_1538) in 
  let t3_1540 : (fp6_t '× fp6_t) :=
    fp12conjugate (f_1532) in 
  let t1_1541 : (fp6_t '× fp6_t) :=
    fp12mul (t3_1540) (t1_1537) in 
  let t1_1542 : (fp6_t '× fp6_t) :=
    fp12conjugate (t1_1541) in 
  let t1_1543 : (fp6_t '× fp6_t) :=
    fp12mul (t1_1542) (t2_1539) in 
  let t2_1544 : (fp6_t '× fp6_t) :=
    fp12exp (t1_1543) (u_1533) in 
  let t2_1545 : (fp6_t '× fp6_t) :=
    fp12conjugate (t2_1544) in 
  let t3_1546 : (fp6_t '× fp6_t) :=
    fp12exp (t2_1545) (u_1533) in 
  let t3_1547 : (fp6_t '× fp6_t) :=
    fp12conjugate (t3_1546) in 
  let t1_1548 : (fp6_t '× fp6_t) :=
    fp12conjugate (t1_1543) in 
  let t3_1549 : (fp6_t '× fp6_t) :=
    fp12mul (t1_1548) (t3_1547) in 
  let t1_1550 : (fp6_t '× fp6_t) :=
    fp12conjugate (t1_1548) in 
  let t1_1551 : (fp6_t '× fp6_t) :=
    frobenius (frobenius (frobenius (t1_1550))) in 
  let t2_1552 : (fp6_t '× fp6_t) :=
    frobenius (frobenius (t2_1545)) in 
  let t1_1553 : (fp6_t '× fp6_t) :=
    fp12mul (t1_1551) (t2_1552) in 
  let t2_1554 : (fp6_t '× fp6_t) :=
    fp12exp (t3_1549) (u_1533) in 
  let t2_1555 : (fp6_t '× fp6_t) :=
    fp12conjugate (t2_1554) in 
  let t2_1556 : (fp6_t '× fp6_t) :=
    fp12mul (t2_1555) (t0_1535) in 
  let t2_1557 : (fp6_t '× fp6_t) :=
    fp12mul (t2_1556) (f_1532) in 
  let t1_1558 : (fp6_t '× fp6_t) :=
    fp12mul (t1_1553) (t2_1557) in 
  let t2_1559 : (fp6_t '× fp6_t) :=
    frobenius (t3_1549) in 
  let t1_1560 : (fp6_t '× fp6_t) :=
    fp12mul (t1_1558) (t2_1559) in 
  t1_1560.


Definition pairing (p_1561 : g1_t) (q_1562 : g2_t)  : fp12_t :=
  let t_1563 : scalar_t :=
    nat_mod_from_literal (
      0x8000000000000000000000000000000000000000000000000000000000000000) (
      @repr WORDSIZE128 15132376222941642752) : scalar_t in 
  let r_1564 : (fp2_t '× fp2_t '× bool) :=
    q_1562 in 
  let f_1565 : (fp6_t '× fp6_t) :=
    fp12fromfp6 (fp6fromfp2 (fp2fromfp (nat_mod_one ))) in 
  let '(r_1564, f_1565) :=
    foldi (usize 1) (usize 64) (fun i_1566 '(r_1564, f_1565) =>
      let lrr_1567 : (fp6_t '× fp6_t) :=
        line_double_p (r_1564) (p_1561) in 
      let r_1564 :=
        g2double (r_1564) in 
      let f_1565 :=
        fp12mul (fp12mul (f_1565) (f_1565)) (lrr_1567) in 
      let '(r_1564, f_1565) :=
        if nat_mod_bit (t_1563) (((usize 64) - (i_1566)) - (
            usize 1)):bool then (let lrq_1568 : (fp6_t '× fp6_t) :=
            line_add_p (r_1564) (q_1562) (p_1561) in 
          let r_1564 :=
            g2add (r_1564) (q_1562) in 
          let f_1565 :=
            fp12mul (f_1565) (lrq_1568) in 
          (r_1564, f_1565)) else ((r_1564, f_1565)) in 
      (r_1564, f_1565))
    (r_1564, f_1565) in 
  final_exponentiation (fp12conjugate (f_1565)).


Definition test_fp2_prop_add_neg (a_1569 : fp2_t)  : bool :=
  let b_1570 : (fp_t '× fp_t) :=
    fp2neg (a_1569) in 
  (fp2fromfp (nat_mod_zero )) =.? (fp2add (a_1569) (b_1570)).

(*QuickChick (
  forAll g_fp2_t (fun a_1569 : fp2_t =>test_fp2_prop_add_neg a_1569)).*)


Definition test_fp2_prop_mul_inv (a_1571 : fp2_t)  : bool :=
  let b_1572 : (fp_t '× fp_t) :=
    fp2inv (a_1571) in 
  (fp2fromfp (nat_mod_one )) =.? (fp2mul (a_1571) (b_1572)).

(*QuickChick (
  forAll g_fp2_t (fun a_1571 : fp2_t =>test_fp2_prop_mul_inv a_1571)).*)


Definition test_extraction_issue   : bool :=
  let b_1573 : (fp_t '× fp_t) :=
    fp2inv ((nat_mod_one , nat_mod_one )) in 
  (fp2fromfp (nat_mod_one )) =.? (fp2mul ((nat_mod_one , nat_mod_one )) (
      b_1573)).

(*QuickChick (test_extraction_issue).*)


Definition test_fp6_prop_mul_inv (a_1574 : fp6_t)  : bool :=
  let b_1575 : (fp2_t '× fp2_t '× fp2_t) :=
    fp6inv (a_1574) in 
  (fp6fromfp2 (fp2fromfp (nat_mod_one ))) =.? (fp6mul (a_1574) (b_1575)).

(*QuickChick (
  forAll g_fp6_t (fun a_1574 : fp6_t =>test_fp6_prop_mul_inv a_1574)).*)


Definition test_fp6_prop_add_neg (a_1576 : fp6_t)  : bool :=
  let b_1577 : (fp2_t '× fp2_t '× fp2_t) :=
    fp6neg (a_1576) in 
  (fp6fromfp2 (fp2fromfp (nat_mod_zero ))) =.? (fp6add (a_1576) (b_1577)).

(*QuickChick (
  forAll g_fp6_t (fun a_1576 : fp6_t =>test_fp6_prop_add_neg a_1576)).*)


Definition test_fp12_prop_add_neg (a_1578 : fp12_t)  : bool :=
  let b_1579 : (fp6_t '× fp6_t) :=
    fp12neg (a_1578) in 
  (fp12fromfp6 (fp6fromfp2 (fp2fromfp (nat_mod_zero )))) =.? (fp12add (a_1578) (
      b_1579)).

(*QuickChick (
  forAll g_fp12_t (fun a_1578 : fp12_t =>test_fp12_prop_add_neg a_1578)).*)


Definition test_fp12_prop_mul_inv (a_1580 : fp12_t)  : bool :=
  let b_1581 : (fp6_t '× fp6_t) :=
    fp12inv (a_1580) in 
  (fp12fromfp6 (fp6fromfp2 (fp2fromfp (nat_mod_one )))) =.? (fp12mul (a_1580) (
      b_1581)).

(*QuickChick (
  forAll g_fp12_t (fun a_1580 : fp12_t =>test_fp12_prop_mul_inv a_1580)).*)


