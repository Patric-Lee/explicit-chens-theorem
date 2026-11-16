import PlattAssemblyKernel
import PlattCertificates.Count131072.C049536
import PlattCertificates.Count131072.C049537
import PlattCertificates.Count131072.C049538
import PlattCertificates.Count131072.C049539
import PlattCertificates.Count131072.C049540
import PlattCertificates.Count131072.C049541
import PlattCertificates.Count131072.C049542
import PlattCertificates.Count131072.C049543
import PlattCertificates.Count131072.C049544
import PlattCertificates.Count131072.C049545
import PlattCertificates.Count131072.C049546
import PlattCertificates.Count131072.C049547
import PlattCertificates.Count131072.C049548
import PlattCertificates.Count131072.C049549
import PlattCertificates.Count131072.C049550
import PlattCertificates.Count131072.C049551
import PlattCertificates.Count131072.C049552
import PlattCertificates.Count131072.C049553
import PlattCertificates.Count131072.C049554
import PlattCertificates.Count131072.C049555
import PlattCertificates.Count131072.C049556
import PlattCertificates.Count131072.C049557
import PlattCertificates.Count131072.C049558
import PlattCertificates.Count131072.C049559
import PlattCertificates.Count131072.C049560
import PlattCertificates.Count131072.C049561
import PlattCertificates.Count131072.C049562
import PlattCertificates.Count131072.C049563
import PlattCertificates.Count131072.C049564
import PlattCertificates.Count131072.C049565
import PlattCertificates.Count131072.C049566
import PlattCertificates.Count131072.C049567
namespace ChenEffective.PlattWindow.Assembly.Prefix.S5.B000298
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts49536 : List PrefixCut := [⟨64,252023232,252023368⟩]
theorem checked49536 : checkPrefixCuts (2^48) 6496714753 10 Manual.Count131072.C049536.packed 64 cuts49536 = true := by
 decide +kernel
def cuts49537 : List PrefixCut := [⟨26,101206438,101206497⟩,
⟨64,251324936,251325081⟩]
theorem checked49537 : checkPrefixCuts (2^48) 6496845825 10 Manual.Count131072.C049537.packed 64 cuts49537 = true := by
 decide +kernel
def pointBounds49537 : List (Nat × Nat × Nat) := [(6496899072,111541108660381,111541495716478)]
theorem point_links_checked49537 : (cuts49537.take 1).map (fun c => (6496845825-1+2*2^10*c.k,111541007453943+c.lower,111541394509981+c.upper)) = pointBounds49537 := by
 decide +kernel
def cuts49538 : List PrefixCut := [⟨62,245341305,245341445⟩,
⟨64,253052820,253052965⟩]
theorem checked49538 : checkPrefixCuts (2^48) 6496976897 10 Manual.Count131072.C049538.packed 64 cuts49538 = true := by
 decide +kernel
def pointBounds49538 : List (Nat × Nat × Nat) := [(6497103872,111541504120184,111541891176507)]
theorem point_links_checked49538 : (cuts49538.take 1).map (fun c => (6496976897-1+2*2^10*c.k,111541258778879+c.lower,111541645835062+c.upper)) = pointBounds49538 := by
 decide +kernel
def cuts49539 : List PrefixCut := [⟨64,253220994,253221140⟩]
theorem checked49539 : checkPrefixCuts (2^48) 6497107969 10 Manual.Count131072.C049539.packed 64 cuts49539 = true := by
 decide +kernel
def cuts49540 : List PrefixCut := [⟨34,131915491,131915573⟩,
⟨64,249793463,249793610⟩]
theorem checked49540 : checkPrefixCuts (2^48) 6497239041 10 Manual.Count131072.C049540.packed 64 cuts49540 = true := by
 decide +kernel
def pointBounds49540 : List (Nat × Nat × Nat) := [(6497308672,111541896968184,111542284024740)]
theorem point_links_checked49540 : (cuts49540.take 1).map (fun c => (6497239041-1+2*2^10*c.k,111541765052693+c.lower,111542152109167+c.upper)) = pointBounds49540 := by
 decide +kernel
def cuts49541 : List PrefixCut := [⟨64,249441876,249442014⟩]
theorem checked49541 : checkPrefixCuts (2^48) 6497370113 10 Manual.Count131072.C049541.packed 64 cuts49541 = true := by
 decide +kernel
def cuts49542 : List PrefixCut := [⟨6,23306398,23306412⟩,
⟨64,255025111,255025253⟩]
theorem checked49542 : checkPrefixCuts (2^48) 6497501185 10 Manual.Count131072.C049542.packed 64 cuts49542 = true := by
 decide +kernel
def pointBounds49542 : List (Nat × Nat × Nat) := [(6497513472,111542287594430,111542674651203)]
theorem point_links_checked49542 : (cuts49542.take 1).map (fun c => (6497501185-1+2*2^10*c.k,111542264288032+c.lower,111542651344791+c.upper)) = pointBounds49542 := by
 decide +kernel
def cuts49543 : List PrefixCut := [⟨42,165913001,165913093⟩,
⟨64,252420818,252420961⟩]
theorem checked49543 : checkPrefixCuts (2^48) 6497632257 10 Manual.Count131072.C049543.packed 64 cuts49543 = true := by
 decide +kernel
def pointBounds49543 : List (Nat × Nat × Nat) := [(6497718272,111542685226144,111543072283137)]
theorem point_links_checked49543 : (cuts49543.take 1).map (fun c => (6497632257-1+2*2^10*c.k,111542519313143+c.lower,111542906370044+c.upper)) = pointBounds49543 := by
 decide +kernel
def cuts49544 : List PrefixCut := [⟨64,251159491,251159632⟩]
theorem checked49544 : checkPrefixCuts (2^48) 6497763329 10 Manual.Count131072.C049544.packed 64 cuts49544 = true := by
 decide +kernel
def cuts49545 : List PrefixCut := [⟨14,54233846,54233878⟩,
⟨64,247689040,247689184⟩]
theorem checked49545 : checkPrefixCuts (2^48) 6497894401 10 Manual.Count131072.C049545.packed 64 cuts49545 = true := by
 decide +kernel
def pointBounds49545 : List (Nat × Nat × Nat) := [(6497923072,111543077127298,111543464184515)]
theorem point_links_checked49545 : (cuts49545.take 1).map (fun c => (6497894401-1+2*2^10*c.k,111543022893452+c.lower,111543409950637+c.upper)) = pointBounds49545 := by
 decide +kernel
def cuts49546 : List PrefixCut := [⟨50,197567220,197567335⟩,
⟨64,250846159,250846303⟩]
theorem checked49546 : checkPrefixCuts (2^48) 6498025473 10 Manual.Count131072.C049546.packed 64 cuts49546 = true := by
 decide +kernel
def pointBounds49546 : List (Nat × Nat × Nat) := [(6498127872,111543468149712,111543855207156)]
theorem point_links_checked49546 : (cuts49546.take 1).map (fun c => (6498025473-1+2*2^10*c.k,111543270582492+c.lower,111543657639821+c.upper)) = pointBounds49546 := by
 decide +kernel
def cuts49547 : List PrefixCut := [⟨64,248761939,248762083⟩]
theorem checked49547 : checkPrefixCuts (2^48) 6498156545 10 Manual.Count131072.C049547.packed 64 cuts49547 = true := by
 decide +kernel
def cuts49548 : List PrefixCut := [⟨22,85330732,85330779⟩,
⟨64,248713612,248713749⟩]
theorem checked49548 : checkPrefixCuts (2^48) 6498287617 10 Manual.Count131072.C049548.packed 64 cuts49548 = true := by
 decide +kernel
def pointBounds49548 : List (Nat × Nat × Nat) := [(6498332672,111543855521322,111544242578986)]
theorem point_links_checked49548 : (cuts49548.take 1).map (fun c => (6498287617-1+2*2^10*c.k,111543770190590+c.lower,111544157248207+c.upper)) = pointBounds49548 := by
 decide +kernel
def cuts49549 : List PrefixCut := [⟨58,228741106,228741236⟩,
⟨64,253169939,253170083⟩]
theorem checked49549 : checkPrefixCuts (2^48) 6498418689 10 Manual.Count131072.C049549.packed 64 cuts49549 = true := by
 decide +kernel
def pointBounds49549 : List (Nat × Nat × Nat) := [(6498537472,111544247645308,111544634703192)]
theorem point_links_checked49549 : (cuts49549.take 1).map (fun c => (6498418689-1+2*2^10*c.k,111544018904202+c.lower,111544405961956+c.upper)) = pointBounds49549 := by
 decide +kernel
def cuts49550 : List PrefixCut := [⟨64,249829721,249829868⟩]
theorem checked49550 : checkPrefixCuts (2^48) 6498549761 10 Manual.Count131072.C049550.packed 64 cuts49550 = true := by
 decide +kernel
def cuts49551 : List PrefixCut := [⟨30,119325704,119325774⟩,
⟨64,251253991,251254134⟩]
theorem checked49551 : checkPrefixCuts (2^48) 6498680833 10 Manual.Count131072.C049551.packed 64 cuts49551 = true := by
 decide +kernel
def pointBounds49551 : List (Nat × Nat × Nat) := [(6498742272,111544641229566,111545028287681)]
theorem point_links_checked49551 : (cuts49551.take 1).map (fun c => (6498680833-1+2*2^10*c.k,111544521903862+c.lower,111544908961907+c.upper)) = pointBounds49551 := by
 decide +kernel
def cuts49552 : List PrefixCut := [⟨64,253197929,253198069⟩]
theorem checked49552 : checkPrefixCuts (2^48) 6498811905 10 Manual.Count131072.C049552.packed 64 cuts49552 = true := by
 decide +kernel
def cuts49553 : List PrefixCut := [⟨2,7579400,7579405⟩,
⟨64,250854033,250854181⟩]
theorem checked49553 : checkPrefixCuts (2^48) 6498942977 10 Manual.Count131072.C049553.packed 64 cuts49553 = true := by
 decide +kernel
def pointBounds49553 : List (Nat × Nat × Nat) := [(6498947072,111545033935182,111545420993515)]
theorem point_links_checked49553 : (cuts49553.take 1).map (fun c => (6498942977-1+2*2^10*c.k,111545026355782+c.lower,111545413414110+c.upper)) = pointBounds49553 := by
 decide +kernel
def cuts49554 : List PrefixCut := [⟨38,151800644,151800730⟩,
⟨64,251715212,251715357⟩]
theorem checked49554 : checkPrefixCuts (2^48) 6499074049 10 Manual.Count131072.C049554.packed 64 cuts49554 = true := by
 decide +kernel
def pointBounds49554 : List (Nat × Nat × Nat) := [(6499151872,111545429010459,111545816069021)]
theorem point_links_checked49554 : (cuts49554.take 1).map (fun c => (6499074049-1+2*2^10*c.k,111545277209815+c.lower,111545664268291+c.upper)) = pointBounds49554 := by
 decide +kernel
def cuts49555 : List PrefixCut := [⟨64,252099878,252100022⟩]
theorem checked49555 : checkPrefixCuts (2^48) 6499205121 10 Manual.Count131072.C049555.packed 64 cuts49555 = true := by
 decide +kernel
def cuts49556 : List PrefixCut := [⟨10,39063983,39064007⟩,
⟨64,249323116,249323258⟩]
theorem checked49556 : checkPrefixCuts (2^48) 6499336193 10 Manual.Count131072.C049556.packed 64 cuts49556 = true := by
 decide +kernel
def pointBounds49556 : List (Nat × Nat × Nat) := [(6499356672,111545820088888,111546207147677)]
theorem point_links_checked49556 : (cuts49556.take 1).map (fun c => (6499336193-1+2*2^10*c.k,111545781024905+c.lower,111546168083670+c.upper)) = pointBounds49556 := by
 decide +kernel
def cuts49557 : List PrefixCut := [⟨46,178425112,178425218⟩,
⟨64,249967665,249967809⟩]
theorem checked49557 : checkPrefixCuts (2^48) 6499467265 10 Manual.Count131072.C049557.packed 64 cuts49557 = true := by
 decide +kernel
def pointBounds49557 : List (Nat × Nat × Nat) := [(6499561472,111546208773133,111546595832146)]
theorem point_links_checked49557 : (cuts49557.take 1).map (fun c => (6499467265-1+2*2^10*c.k,111546030348021+c.lower,111546417406928+c.upper)) = pointBounds49557 := by
 decide +kernel
def cuts49558 : List PrefixCut := [⟨64,250915375,250915522⟩]
theorem checked49558 : checkPrefixCuts (2^48) 6499598337 10 Manual.Count131072.C049558.packed 64 cuts49558 = true := by
 decide +kernel
def cuts49559 : List PrefixCut := [⟨18,71973754,71973797⟩,
⟨64,256193535,256193677⟩]
theorem checked49559 : checkPrefixCuts (2^48) 6499729409 10 Manual.Count131072.C049559.packed 64 cuts49559 = true := by
 decide +kernel
def pointBounds49559 : List (Nat × Nat × Nat) := [(6499766272,111546603204815,111546990264056)]
theorem point_links_checked49559 : (cuts49559.take 1).map (fun c => (6499729409-1+2*2^10*c.k,111546531231061+c.lower,111546918290259+c.upper)) = pointBounds49559 := by
 decide +kernel
def cuts49560 : List PrefixCut := [⟨54,208337420,208337539⟩,
⟨64,247181066,247181210⟩]
theorem checked49560 : checkPrefixCuts (2^48) 6499860481 10 Manual.Count131072.C049560.packed 64 cuts49560 = true := by
 decide +kernel
def pointBounds49560 : List (Nat × Nat × Nat) := [(6499971072,111546995762016,111547382821475)]
theorem point_links_checked49560 : (cuts49560.take 1).map (fun c => (6499860481-1+2*2^10*c.k,111546787424596+c.lower,111547174483936+c.upper)) = pointBounds49560 := by
 decide +kernel
def cuts49561 : List PrefixCut := [⟨64,252329230,252329376⟩]
theorem checked49561 : checkPrefixCuts (2^48) 6499991553 10 Manual.Count131072.C049561.packed 64 cuts49561 = true := by
 decide +kernel
def cuts49562 : List PrefixCut := [⟨26,102541109,102541165⟩,
⟨64,251328156,251328299⟩]
theorem checked49562 : checkPrefixCuts (2^48) 6500122625 10 Manual.Count131072.C049562.packed 64 cuts49562 = true := by
 decide +kernel
def pointBounds49562 : List (Nat × Nat × Nat) := [(6500175872,111547389476001,111547776535687)]
theorem point_links_checked49562 : (cuts49562.take 1).map (fun c => (6500122625-1+2*2^10*c.k,111547286934892+c.lower,111547673994522+c.upper)) = pointBounds49562 := by
 decide +kernel
def cuts49563 : List PrefixCut := [⟨62,244135088,244135230⟩,
⟨64,251193197,251193343⟩]
theorem checked49563 : checkPrefixCuts (2^48) 6500253697 10 Manual.Count131072.C049563.packed 64 cuts49563 = true := by
 decide +kernel
def pointBounds49563 : List (Nat × Nat × Nat) := [(6500380672,111547782398136,111548169458051)]
theorem point_links_checked49563 : (cuts49563.take 1).map (fun c => (6500253697-1+2*2^10*c.k,111547538263048+c.lower,111547925322821+c.upper)) = pointBounds49563 := by
 decide +kernel
def cuts49564 : List PrefixCut := [⟨64,251924202,251924352⟩]
theorem checked49564 : checkPrefixCuts (2^48) 6500384769 10 Manual.Count131072.C049564.packed 64 cuts49564 = true := by
 decide +kernel
def cuts49565 : List PrefixCut := [⟨34,134187210,134187283⟩,
⟨64,251529458,251529597⟩]
theorem checked49565 : checkPrefixCuts (2^48) 6500515841 10 Manual.Count131072.C049565.packed 64 cuts49565 = true := by
 decide +kernel
def pointBounds49565 : List (Nat × Nat × Nat) := [(6500585472,111548175567657,111548562627799)]
theorem point_links_checked49565 : (cuts49565.take 1).map (fun c => (6500515841-1+2*2^10*c.k,111548041380447+c.lower,111548428440516+c.upper)) = pointBounds49565 := by
 decide +kernel
def cuts49566 : List PrefixCut := [⟨64,249229530,249229675⟩]
theorem checked49566 : checkPrefixCuts (2^48) 6500646913 10 Manual.Count131072.C049566.packed 64 cuts49566 = true := by
 decide +kernel
def cuts49567 : List PrefixCut := [⟨6,24593609,24593622⟩,
⟨64,250913152,250913295⟩]
theorem checked49567 : checkPrefixCuts (2^48) 6500777985 10 Manual.Count131072.C049567.packed 64 cuts49567 = true := by
 decide +kernel
def pointBounds49567 : List (Nat × Nat × Nat) := [(6500790272,111548566733044,111548953793410)]
theorem point_links_checked49567 : (cuts49567.take 1).map (fun c => (6500777985-1+2*2^10*c.k,111548542139435+c.lower,111548929199788+c.upper)) = pointBounds49567 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S5.B000298
