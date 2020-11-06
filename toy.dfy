class Global{
  var N_LAS: int;
  var N_PAS: int;
  var N_DIFF: int;
  var las: array<int>;
  var pas: array<int>;
  var l2p_ram: array<int>;
  var l2p_flash: array<int>;
  var p: int;

  predicate init()
  reads this;
  reads las, pas, l2p_ram, l2p_flash;
  {
         N_LAS == 4000000
      && N_PAS == 6000000
      && N_DIFF == 4000000
      && 0 <= p <= N_DIFF
      && las.Length == N_DIFF
      && pas.Length == N_DIFF
      && l2p_flash.Length == N_LAS
      && l2p_ram.Length == N_LAS
      && forall k: int :: 0 <= k < N_DIFF ==> las[k] == 0
      && forall k: int :: 0 <= k < N_DIFF ==> pas[k] == 0
      && forall k: int :: 0 <= k < N_LAS ==> l2p_ram[k] == 0
      && forall k: int :: 0 <= k < N_LAS ==> l2p_flash[k] == 0
  }
  predicate inv()
  reads this;
  {
    p < las.Length
  }
}

//method write (global0: Global, la: int, pa: int) returns (global1: Global)
//  modifies global0.l2p_ram;
//  modifies global0.las;
//  modifies global0.pas;
//  modifies global0;
//  requires global0.init();
//  ensures 0 <= global1.p < global1.N_DIFF
//  ensures la >= global0.N_LAS || pa >= global0.N_PAS ==> global0 == global1;
//  ensures global1.l2p_flash.Length == global1.N_LAS == global1.l2p_ram.Length
//  ensures la < global0.N_LAS && pa < global0.N_PAS ==>
//    global1.p == global1.N_DIFF - 1 ==> forall k: int :: 0 <= k < global1.N_LAS ==> global1.l2p_flash[k] == global1.l2p_ram[k]
//{
//    global1 := global0;
//    assert 0 <= global1.p < global1.N_DIFF;
//    assert global1.l2p_flash.Length == global1.N_LAS;
//    assert global1.l2p_ram.Length == global1.N_LAS;
//    if (la >= global1.N_LAS || pa >= global1.N_PAS)
//      { return global1; }
//    assert la < global0.N_LAS && pa < global1.N_PAS;
//    global1.l2p_ram[global1.p] := pa;
//    global1.las[global1.p] := la;
//    global1.pas[global1.p] := pa;
//    global1.p := global1.p + 1;
//    if (global1.p == global1.N_DIFF)
//      {
//          global1.p := 0;
//          var i := 0;
//          while (i < global1.N_LAS)
//            invariant forall k: int :: 0 <= k < global1.N_LAS ==> global1.l2p_flash[k] == global1.l2p_ram[k]
//          {
//              global1.l2p_flash[i] :=  global1.l2p_ram[i];
//              i := i + 1;
//          }
//      }
//    //assert global0.p < global0.N_DIFF ==> global1.p == global0.p + 1;
//    assert global0.p == global0.N_DIFF ==> global1.p < global0.p + 1;
//    return global1;
//}

lemma RI(global: Global)
  requires global.init()
  requires global.inv()
  //ensures global.p < global.N_DIFF
  //ensures global.las.Length == global.N_DIFF
  //ensures global.p < global.las.Length
  //ensures forall la ::
  //  (exists i :: i < global.p && global.las[i] == la) ==> 
  //    (exists i :: i < global.p
  //              && global.las[i] == la
  //              && (forall j :: j > i ==> !(global.las[j] == la))
  //              && global.l2p_ram[la] == global.pas[i]);
{
  var i := 0;
  var j := 0;
  var jj := j;
  var la := 0;
//  while (i < global.p)
//  {
    la := global.las[i];
    assert 0 <= global.p <= global.N_DIFF;
    var flag := false;
    while (j < global.p)
      invariant 0 <= i <= jj < global.las.Length
      invariant jj <= global.p
      invariant global.las[i] == la
      invariant notin(i, jj, la, global.las)
      invariant 0 <= j <= global.p
      invariant flag == true ==> jj == j - 1
    {
      flag := true;
      jj := j;
      if (global.las[jj] == la)
      {
        i := jj;
      }
      j := j + 1;
    }
    assert j == global.p;
    assert flag == true ==> jj == global.p - 1;
    //i := i + 1;
//}
  //assert 0 <= i <= global.p;
  //assert global.p < global.las.Length;
  //assert jj <= global.p < global.las.Length;
  assert jj <= global.p;
  assert flag == true ==> notin(i, global.p, la, global.las);
  //assert 0 <= i <= jj < global.las.Length;
  //assert exists i | 0 <= i <= jj < global.las.Length :: notin(i, jj, la, global.las);
}

predicate notin(i: int, j: int, la: int, arr: array<int>)
  requires 0 <= i <= j < arr.Length
  reads arr
{
  forall k | i < k < j :: arr[k] != la
}