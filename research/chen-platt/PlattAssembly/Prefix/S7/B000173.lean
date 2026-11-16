import PlattAssemblyKernel
import PlattCertificates.Count131072.C065536
import PlattCertificates.Count131072.C065537
import PlattCertificates.Count131072.C065538
import PlattCertificates.Count131072.C065539
import PlattCertificates.Count131072.C065540
import PlattCertificates.Count131072.C065541
import PlattCertificates.Count131072.C065542
import PlattCertificates.Count131072.C065543
import PlattCertificates.Count131072.C065544
import PlattCertificates.Count131072.C065545
import PlattCertificates.Count131072.C065546
import PlattCertificates.Count131072.C065547
import PlattCertificates.Count131072.C065548
import PlattCertificates.Count131072.C065549
import PlattCertificates.Count131072.C065550
import PlattCertificates.Count131072.C065551
import PlattCertificates.Count131072.C065552
import PlattCertificates.Count131072.C065553
import PlattCertificates.Count131072.C065554
import PlattCertificates.Count131072.C065555
import PlattCertificates.Count131072.C065556
import PlattCertificates.Count131072.C065557
import PlattCertificates.Count131072.C065558
import PlattCertificates.Count131072.C065559
import PlattCertificates.Count131072.C065560
import PlattCertificates.Count131072.C065561
import PlattCertificates.Count131072.C065562
import PlattCertificates.Count131072.C065563
import PlattCertificates.Count131072.C065564
import PlattCertificates.Count131072.C065565
import PlattCertificates.Count131072.C065566
import PlattCertificates.Count131072.C065567
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000173
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts65536 : List PrefixCut := [⟨64,186035608,186035717⟩]
theorem checked65536 : checkPrefixCuts (2^48) 8593866753 10 Manual.Count131072.C065536.packed 64 cuts65536 = true := by
 decide +kernel
def cuts65537 : List PrefixCut := [⟨51,149252222,149252313⟩,
⟨64,186294789,186294902⟩]
theorem checked65537 : checkPrefixCuts (2^48) 8593997825 10 Manual.Count131072.C065537.packed 64 cuts65537 = true := by
 decide +kernel
def pointBounds65537 : List (Nat × Nat × Nat) := [(8594102272,115004799764351,115005188797197)]
theorem point_links_checked65537 : (cuts65537.take 1).map (fun c => (8593997825-1+2*2^10*c.k,115004650512129+c.lower,115005039544884+c.upper)) = pointBounds65537 := by
 decide +kernel
def cuts65538 : List PrefixCut := [⟨64,187798523,187798627⟩]
theorem checked65538 : checkPrefixCuts (2^48) 8594128897 10 Manual.Count131072.C065538.packed 64 cuts65538 = true := by
 decide +kernel
def cuts65539 : List PrefixCut := [⟨55,162970388,162970483⟩,
⟨64,188286938,188287047⟩]
theorem checked65539 : checkPrefixCuts (2^48) 8594259969 10 Manual.Count131072.C065539.packed 64 cuts65539 = true := by
 decide +kernel
def pointBounds65539 : List (Nat × Nat × Nat) := [(8594372608,115005187575829,115005576608896)]
theorem point_links_checked65539 : (cuts65539.take 1).map (fun c => (8594259969-1+2*2^10*c.k,115005024605441+c.lower,115005413638413+c.upper)) = pointBounds65539 := by
 decide +kernel
def cuts65540 : List PrefixCut := [⟨64,186057000,186057105⟩]
theorem checked65540 : checkPrefixCuts (2^48) 8594391041 10 Manual.Count131072.C065540.packed 64 cuts65540 = true := by
 decide +kernel
def cuts65541 : List PrefixCut := [⟨59,172135419,172135520⟩,
⟨64,187495178,187495288⟩]
theorem checked65541 : checkPrefixCuts (2^48) 8594522113 10 Manual.Count131072.C065541.packed 64 cuts65541 = true := by
 decide +kernel
def pointBounds65541 : List (Nat × Nat × Nat) := [(8594642944,115005571084798,115005960118085)]
theorem point_links_checked65541 : (cuts65541.take 1).map (fun c => (8594522113-1+2*2^10*c.k,115005398949379+c.lower,115005787982565+c.upper)) = pointBounds65541 := by
 decide +kernel
def cuts65542 : List PrefixCut := [⟨64,186247832,186247942⟩]
theorem checked65542 : checkPrefixCuts (2^48) 8594653185 10 Manual.Count131072.C065542.packed 64 cuts65542 = true := by
 decide +kernel
def cuts65543 : List PrefixCut := [⟨63,184181805,184181914⟩,
⟨64,187489455,187489565⟩]
theorem checked65543 : checkPrefixCuts (2^48) 8594784257 10 Manual.Count131072.C065543.packed 64 cuts65543 = true := by
 decide +kernel
def pointBounds65543 : List (Nat × Nat × Nat) := [(8594913280,115005956874194,115006345907709)]
theorem point_links_checked65543 : (cuts65543.take 1).map (fun c => (8594784257-1+2*2^10*c.k,115005772692389+c.lower,115006161725795+c.upper)) = pointBounds65543 := by
 decide +kernel
def cuts65544 : List PrefixCut := [⟨64,187977839,187977955⟩]
theorem checked65544 : checkPrefixCuts (2^48) 8594915329 10 Manual.Count131072.C065544.packed 64 cuts65544 = true := by
 decide +kernel
def cuts65545 : List PrefixCut := [⟨64,189088418,189088529⟩]
theorem checked65545 : checkPrefixCuts (2^48) 8595046401 10 Manual.Count131072.C065545.packed 64 cuts65545 = true := by
 decide +kernel
def cuts65546 : List PrefixCut := [⟨3,8317990,8317995⟩,
⟨64,188463314,188463420⟩]
theorem checked65546 : checkPrefixCuts (2^48) 8595177473 10 Manual.Count131072.C065546.packed 64 cuts65546 = true := by
 decide +kernel
def pointBounds65546 : List (Nat × Nat × Nat) := [(8595183616,115006345566091,115006734599839)]
theorem point_links_checked65546 : (cuts65546.take 1).map (fun c => (8595177473-1+2*2^10*c.k,115006337248101+c.lower,115006726281844+c.upper)) = pointBounds65546 := by
 decide +kernel
def cuts65547 : List PrefixCut := [⟨64,183744839,183744950⟩]
theorem checked65547 : checkPrefixCuts (2^48) 8595308545 10 Manual.Count131072.C065547.packed 64 cuts65547 = true := by
 decide +kernel
def cuts65548 : List PrefixCut := [⟨7,21056306,21056318⟩,
⟨64,189439977,189440087⟩]
theorem checked65548 : checkPrefixCuts (2^48) 8595439617 10 Manual.Count131072.C065548.packed 64 cuts65548 = true := by
 decide +kernel
def pointBounds65548 : List (Nat × Nat × Nat) := [(8595453952,115006730512560,115007119546532)]
theorem point_links_checked65548 : (cuts65548.take 1).map (fun c => (8595439617-1+2*2^10*c.k,115006709456254+c.lower,115007098490214+c.upper)) = pointBounds65548 := by
 decide +kernel
def cuts65549 : List PrefixCut := [⟨64,189404322,189404433⟩]
theorem checked65549 : checkPrefixCuts (2^48) 8595570689 10 Manual.Count131072.C065549.packed 64 cuts65549 = true := by
 decide +kernel
def cuts65550 : List PrefixCut := [⟨11,32647723,32647743⟩,
⟨64,187665931,187666048⟩]
theorem checked65550 : checkPrefixCuts (2^48) 8595701761 10 Manual.Count131072.C065550.packed 64 cuts65550 = true := by
 decide +kernel
def pointBounds65550 : List (Nat × Nat × Nat) := [(8595724288,115007120948276,115007509982477)]
theorem point_links_checked65550 : (cuts65550.take 1).map (fun c => (8595701761-1+2*2^10*c.k,115007088300553+c.lower,115007477334734+c.upper)) = pointBounds65550 := by
 decide +kernel
def cuts65551 : List PrefixCut := [⟨64,187859544,187859649⟩]
theorem checked65551 : checkPrefixCuts (2^48) 8595832833 10 Manual.Count131072.C065551.packed 64 cuts65551 = true := by
 decide +kernel
def cuts65552 : List PrefixCut := [⟨15,43779996,43780019⟩,
⟨64,187005308,187005412⟩]
theorem checked65552 : checkPrefixCuts (2^48) 8595963905 10 Manual.Count131072.C065552.packed 64 cuts65552 = true := by
 decide +kernel
def pointBounds65552 : List (Nat × Nat × Nat) := [(8595994624,115007507606024,115007896640450)]
theorem point_links_checked65552 : (cuts65552.take 1).map (fun c => (8595963905-1+2*2^10*c.k,115007463826028+c.lower,115007852860431+c.upper)) = pointBounds65552 := by
 decide +kernel
def cuts65553 : List PrefixCut := [⟨64,187395395,187395506⟩]
theorem checked65553 : checkPrefixCuts (2^48) 8596094977 10 Manual.Count131072.C065553.packed 64 cuts65553 = true := by
 decide +kernel
def cuts65554 : List PrefixCut := [⟨19,55271758,55271791⟩,
⟨64,187981905,187982014⟩]
theorem checked65554 : checkPrefixCuts (2^48) 8596226049 10 Manual.Count131072.C065554.packed 64 cuts65554 = true := by
 decide +kernel
def pointBounds65554 : List (Nat × Nat × Nat) := [(8596264960,115007893498489,115008282533140)]
theorem point_links_checked65554 : (cuts65554.take 1).map (fun c => (8596226049-1+2*2^10*c.k,115007838226731+c.lower,115008227261349+c.upper)) = pointBounds65554 := by
 decide +kernel
def cuts65555 : List PrefixCut := [⟨64,188142762,188142864⟩]
theorem checked65555 : checkPrefixCuts (2^48) 8596357121 10 Manual.Count131072.C065555.packed 64 cuts65555 = true := by
 decide +kernel
def cuts65556 : List PrefixCut := [⟨23,68432700,68432742⟩,
⟨64,189547832,189547940⟩]
theorem checked65556 : checkPrefixCuts (2^48) 8596488193 10 Manual.Count131072.C065556.packed 64 cuts65556 = true := by
 decide +kernel
def pointBounds65556 : List (Nat × Nat × Nat) := [(8596535296,115008282784098,115008671818969)]
theorem point_links_checked65556 : (cuts65556.take 1).map (fun c => (8596488193-1+2*2^10*c.k,115008214351398+c.lower,115008603386227+c.upper)) = pointBounds65556 := by
 decide +kernel
def cuts65557 : List PrefixCut := [⟨64,190592699,190592808⟩]
theorem checked65557 : checkPrefixCuts (2^48) 8596619265 10 Manual.Count131072.C065557.packed 64 cuts65557 = true := by
 decide +kernel
def cuts65558 : List PrefixCut := [⟨27,76747025,76747071⟩,
⟨64,184794489,184794602⟩]
theorem checked65558 : checkPrefixCuts (2^48) 8596750337 10 Manual.Count131072.C065558.packed 64 cuts65558 = true := by
 decide +kernel
def pointBounds65558 : List (Nat × Nat × Nat) := [(8596805632,115008671238954,115009060274046)]
theorem point_links_checked65558 : (cuts65558.take 1).map (fun c => (8596750337-1+2*2^10*c.k,115008594491929+c.lower,115008983526975+c.upper)) = pointBounds65558 := by
 decide +kernel
def cuts65559 : List PrefixCut := [⟨64,188622414,188622530⟩]
theorem checked65559 : checkPrefixCuts (2^48) 8596881409 10 Manual.Count131072.C065559.packed 64 cuts65559 = true := by
 decide +kernel
def cuts65560 : List PrefixCut := [⟨31,91445309,91445361⟩,
⟨64,188881464,188881570⟩]
theorem checked65560 : checkPrefixCuts (2^48) 8597012481 10 Manual.Count131072.C065560.packed 64 cuts65560 = true := by
 decide +kernel
def pointBounds65560 : List (Nat × Nat × Nat) := [(8597075968,115009059354141,115009448389468)]
theorem point_links_checked65560 : (cuts65560.take 1).map (fun c => (8597012481-1+2*2^10*c.k,115008967908832+c.lower,115009356944107+c.upper)) = pointBounds65560 := by
 decide +kernel
def cuts65561 : List PrefixCut := [⟨64,184589611,184589720⟩]
theorem checked65561 : checkPrefixCuts (2^48) 8597143553 10 Manual.Count131072.C065561.packed 64 cuts65561 = true := by
 decide +kernel
def cuts65562 : List PrefixCut := [⟨35,100445950,100446010⟩,
⟨64,184161181,184161290⟩]
theorem checked65562 : checkPrefixCuts (2^48) 8597274625 10 Manual.Count131072.C065562.packed 64 cuts65562 = true := by
 decide +kernel
def pointBounds65562 : List (Nat × Nat × Nat) := [(8597346304,115009441825857,115009830861407)]
theorem point_links_checked65562 : (cuts65562.take 1).map (fun c => (8597274625-1+2*2^10*c.k,115009341379907+c.lower,115009730415397+c.upper)) = pointBounds65562 := by
 decide +kernel
def cuts65563 : List PrefixCut := [⟨64,187465032,187465143⟩]
theorem checked65563 : checkPrefixCuts (2^48) 8597405697 10 Manual.Count131072.C065563.packed 64 cuts65563 = true := by
 decide +kernel
def cuts65564 : List PrefixCut := [⟨39,114291370,114291433⟩,
⟨64,187855038,187855142⟩]
theorem checked65564 : checkPrefixCuts (2^48) 8597536769 10 Manual.Count131072.C065564.packed 64 cuts65564 = true := by
 decide +kernel
def pointBounds65564 : List (Nat × Nat × Nat) := [(8597616640,115009827297490,115010216333263)]
theorem point_links_checked65564 : (cuts65564.take 1).map (fun c => (8597536769-1+2*2^10*c.k,115009713006120+c.lower,115010102041830+c.upper)) = pointBounds65564 := by
 decide +kernel
def cuts65565 : List PrefixCut := [⟨64,187917647,187917757⟩]
theorem checked65565 : checkPrefixCuts (2^48) 8597667841 10 Manual.Count131072.C065565.packed 64 cuts65565 = true := by
 decide +kernel
def cuts65566 : List PrefixCut := [⟨43,127252021,127252089⟩,
⟨64,186867193,186867295⟩]
theorem checked65566 : checkPrefixCuts (2^48) 8597798913 10 Manual.Count131072.C065566.packed 64 cuts65566 = true := by
 decide +kernel
def pointBounds65566 : List (Nat × Nat × Nat) := [(8597886976,115010216030826,115010605066818)]
theorem point_links_checked65566 : (cuts65566.take 1).map (fun c => (8597798913-1+2*2^10*c.k,115010088778805+c.lower,115010477814729+c.upper)) = pointBounds65566 := by
 decide +kernel
def cuts65567 : List PrefixCut := [⟨64,190105331,190105436⟩]
theorem checked65567 : checkPrefixCuts (2^48) 8597929985 10 Manual.Count131072.C065567.packed 64 cuts65567 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000173
