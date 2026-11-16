import PlattAssemblyKernel
import PlattCertificates.Count131072.C040512
import PlattCertificates.Count131072.C040513
import PlattCertificates.Count131072.C040514
import PlattCertificates.Count131072.C040515
import PlattCertificates.Count131072.C040516
import PlattCertificates.Count131072.C040517
import PlattCertificates.Count131072.C040518
import PlattCertificates.Count131072.C040519
import PlattCertificates.Count131072.C040520
import PlattCertificates.Count131072.C040521
import PlattCertificates.Count131072.C040522
import PlattCertificates.Count131072.C040523
import PlattCertificates.Count131072.C040524
import PlattCertificates.Count131072.C040525
import PlattCertificates.Count131072.C040526
import PlattCertificates.Count131072.C040527
import PlattCertificates.Count131072.C040528
import PlattCertificates.Count131072.C040529
import PlattCertificates.Count131072.C040530
import PlattCertificates.Count131072.C040531
import PlattCertificates.Count131072.C040532
import PlattCertificates.Count131072.C040533
import PlattCertificates.Count131072.C040534
import PlattCertificates.Count131072.C040535
import PlattCertificates.Count131072.C040536
import PlattCertificates.Count131072.C040537
import PlattCertificates.Count131072.C040538
import PlattCertificates.Count131072.C040539
import PlattCertificates.Count131072.C040540
import PlattCertificates.Count131072.C040541
import PlattCertificates.Count131072.C040542
import PlattCertificates.Count131072.C040543
namespace ChenEffective.PlattWindow.Assembly.Prefix.S5.B000016
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts40512 : List PrefixCut := [⟨15,72355911,72355954⟩,
⟨64,311296978,311297162⟩]
theorem checked40512 : checkPrefixCuts (2^48) 5313921025 10 Manual.Count131072.C040512.packed 64 cuts40512 = true := by
 decide +kernel
def pointBounds40512 : List (Nat × Nat × Nat) := [(5313951744,109026099347287,109026484947780)]
theorem point_links_checked40512 : (cuts40512.take 1).map (fun c => (5313921025-1+2*2^10*c.k,109026026991376+c.lower,109026412591826+c.upper)) = pointBounds40512 := by
 decide +kernel
def cuts40513 : List PrefixCut := [⟨33,158161548,158161642⟩,
⟨64,308587953,308588134⟩]
theorem checked40513 : checkPrefixCuts (2^48) 5314052097 10 Manual.Count131072.C040513.packed 64 cuts40513 = true := by
 decide +kernel
def pointBounds40513 : List (Nat × Nat × Nat) := [(5314119680,109026496449902,109026882050630)]
theorem point_links_checked40513 : (cuts40513.take 1).map (fun c => (5314052097-1+2*2^10*c.k,109026338288354+c.lower,109026723888988+c.upper)) = pointBounds40513 := by
 decide +kernel
def cuts40514 : List PrefixCut := [⟨51,245074642,245074782⟩,
⟨64,307997724,307997900⟩]
theorem checked40514 : checkPrefixCuts (2^48) 5314183169 10 Manual.Count131072.C040514.packed 64 cuts40514 = true := by
 decide +kernel
def pointBounds40514 : List (Nat × Nat × Nat) := [(5314287616,109026891950949,109027277551904)]
theorem point_links_checked40514 : (cuts40514.take 1).map (fun c => (5314183169-1+2*2^10*c.k,109026646876307+c.lower,109027032477122+c.upper)) = pointBounds40514 := by
 decide +kernel
def cuts40515 : List PrefixCut := [⟨64,308572747,308572928⟩]
theorem checked40515 : checkPrefixCuts (2^48) 5314314241 10 Manual.Count131072.C040515.packed 64 cuts40515 = true := by
 decide +kernel
def cuts40516 : List PrefixCut := [⟨5,25210894,25210910⟩,
⟨64,312166653,312166841⟩]
theorem checked40516 : checkPrefixCuts (2^48) 5314445313 10 Manual.Count131072.C040516.packed 64 cuts40516 = true := by
 decide +kernel
def pointBounds40516 : List (Nat × Nat × Nat) := [(5314455552,109027288657672,109027674258860)]
theorem point_links_checked40516 : (cuts40516.take 1).map (fun c => (5314445313-1+2*2^10*c.k,109027263446778+c.lower,109027649047950+c.upper)) = pointBounds40516 := by
 decide +kernel
def cuts40517 : List PrefixCut := [⟨23,109632526,109632594⟩,
⟨64,304691283,304691462⟩]
theorem checked40517 : checkPrefixCuts (2^48) 5314576385 10 Manual.Count131072.C040517.packed 64 cuts40517 = true := by
 decide +kernel
def pointBounds40517 : List (Nat × Nat × Nat) := [(5314623488,109027685245957,109028070847385)]
theorem point_links_checked40517 : (cuts40517.take 1).map (fun c => (5314576385-1+2*2^10*c.k,109027575613431+c.lower,109027961214791+c.upper)) = pointBounds40517 := by
 decide +kernel
def cuts40518 : List PrefixCut := [⟨41,203105754,203105870⟩,
⟨64,314852269,314852448⟩]
theorem checked40518 : checkPrefixCuts (2^48) 5314707457 10 Manual.Count131072.C040518.packed 64 cuts40518 = true := by
 decide +kernel
def pointBounds40518 : List (Nat × Nat × Nat) := [(5314791424,109028083410468,109028469012123)]
theorem point_links_checked40518 : (cuts40518.take 1).map (fun c => (5314707457-1+2*2^10*c.k,109027880304714+c.lower,109028265906253+c.upper)) = pointBounds40518 := by
 decide +kernel
def cuts40519 : List PrefixCut := [⟨59,288735734,288735905⟩,
⟨64,312726134,312726319⟩]
theorem checked40519 : checkPrefixCuts (2^48) 5314838529 10 Manual.Count131072.C040519.packed 64 cuts40519 = true := by
 decide +kernel
def pointBounds40519 : List (Nat × Nat × Nat) := [(5314959360,109028483892717,109028869494606)]
theorem point_links_checked40519 : (cuts40519.take 1).map (fun c => (5314838529-1+2*2^10*c.k,109028195156983+c.lower,109028580758701+c.upper)) = pointBounds40519 := by
 decide +kernel
def cuts40520 : List PrefixCut := [⟨64,304880565,304880745⟩]
theorem checked40520 : checkPrefixCuts (2^48) 5314969601 10 Manual.Count131072.C040520.packed 64 cuts40520 = true := by
 decide +kernel
def cuts40521 : List PrefixCut := [⟨13,61218819,61218857⟩,
⟨64,308315275,308315463⟩]
theorem checked40521 : checkPrefixCuts (2^48) 5315100673 10 Manual.Count131072.C040521.packed 64 cuts40521 = true := by
 decide +kernel
def pointBounds40521 : List (Nat × Nat × Nat) := [(5315127296,109028873982501,109029259584622)]
theorem point_links_checked40521 : (cuts40521.take 1).map (fun c => (5315100673-1+2*2^10*c.k,109028812763682+c.lower,109029198365765+c.upper)) = pointBounds40521 := by
 decide +kernel
def cuts40522 : List PrefixCut := [⟨31,152830913,152831000⟩,
⟨64,312967762,312967945⟩]
theorem checked40522 : checkPrefixCuts (2^48) 5315231745 10 Manual.Count131072.C040522.packed 64 cuts40522 = true := by
 decide +kernel
def pointBounds40522 : List (Nat × Nat × Nat) := [(5315295232,109029273909870,109029659512228)]
theorem point_links_checked40522 : (cuts40522.take 1).map (fun c => (5315231745-1+2*2^10*c.k,109029121078957+c.lower,109029506681228+c.upper)) = pointBounds40522 := by
 decide +kernel
def cuts40523 : List PrefixCut := [⟨49,238189221,238189363⟩,
⟨64,309570969,309571156⟩]
theorem checked40523 : checkPrefixCuts (2^48) 5315362817 10 Manual.Count131072.C040523.packed 64 cuts40523 = true := by
 decide +kernel
def pointBounds40523 : List (Nat × Nat × Nat) := [(5315463168,109029672235940,109030057838536)]
theorem point_links_checked40523 : (cuts40523.take 1).map (fun c => (5315362817-1+2*2^10*c.k,109029434046719+c.lower,109029819649173+c.upper)) = pointBounds40523 := by
 decide +kernel
def cuts40524 : List PrefixCut := [⟨64,307921766,307921950⟩]
theorem checked40524 : checkPrefixCuts (2^48) 5315493889 10 Manual.Count131072.C040524.packed 64 cuts40524 = true := by
 decide +kernel
def cuts40525 : List PrefixCut := [⟨3,15515033,15515042⟩,
⟨64,308549600,308549782⟩]
theorem checked40525 : checkPrefixCuts (2^48) 5315624961 10 Manual.Count131072.C040525.packed 64 cuts40525 = true := by
 decide +kernel
def pointBounds40525 : List (Nat × Nat × Nat) := [(5315631104,109030067054487,109030452657321)]
theorem point_links_checked40525 : (cuts40525.take 1).map (fun c => (5315624961-1+2*2^10*c.k,109030051539454+c.lower,109030437142279+c.upper)) = pointBounds40525 := by
 decide +kernel
def cuts40526 : List PrefixCut := [⟨21,101665618,101665677⟩,
⟨64,307165304,307165484⟩]
theorem checked40526 : checkPrefixCuts (2^48) 5315756033 10 Manual.Count131072.C040526.packed 64 cuts40526 = true := by
 decide +kernel
def pointBounds40526 : List (Nat × Nat × Nat) := [(5315799040,109030461754672,109030847357738)]
theorem point_links_checked40526 : (cuts40526.take 1).map (fun c => (5315756033-1+2*2^10*c.k,109030360089054+c.lower,109030745692061+c.upper)) = pointBounds40526 := by
 decide +kernel
def cuts40527 : List PrefixCut := [⟨39,191094218,191094329⟩,
⟨64,309805199,309805380⟩]
theorem checked40527 : checkPrefixCuts (2^48) 5315887105 10 Manual.Count131072.C040527.packed 64 cuts40527 = true := by
 decide +kernel
def pointBounds40527 : List (Nat × Nat × Nat) := [(5315966976,109030858348576,109031243951874)]
theorem point_links_checked40527 : (cuts40527.take 1).map (fun c => (5315887105-1+2*2^10*c.k,109030667254358+c.lower,109031052857545+c.upper)) = pointBounds40527 := by
 decide +kernel
def cuts40528 : List PrefixCut := [⟨57,279247058,279247221⟩,
⟨64,314033375,314033558⟩]
theorem checked40528 : checkPrefixCuts (2^48) 5316018177 10 Manual.Count131072.C040528.packed 64 cuts40528 = true := by
 decide +kernel
def pointBounds40528 : List (Nat × Nat × Nat) := [(5316134912,109031256306615,109031641910146)]
theorem point_links_checked40528 : (cuts40528.take 1).map (fun c => (5316018177-1+2*2^10*c.k,109030977059557+c.lower,109031362662925+c.upper)) = pointBounds40528 := by
 decide +kernel
def cuts40529 : List PrefixCut := [⟨64,313231418,313231603⟩]
theorem checked40529 : checkPrefixCuts (2^48) 5316149249 10 Manual.Count131072.C040529.packed 64 cuts40529 = true := by
 decide +kernel
def cuts40530 : List PrefixCut := [⟨11,54322312,54322343⟩,
⟨64,314706185,314706372⟩]
theorem checked40530 : checkPrefixCuts (2^48) 5316280321 10 Manual.Count131072.C040530.packed 64 cuts40530 = true := by
 decide +kernel
def pointBounds40530 : List (Nat × Nat × Nat) := [(5316302848,109031658646662,109032044250429)]
theorem point_links_checked40530 : (cuts40530.take 1).map (fun c => (5316280321-1+2*2^10*c.k,109031604324350+c.lower,109031989928086+c.upper)) = pointBounds40530 := by
 decide +kernel
def cuts40531 : List PrefixCut := [⟨29,140937534,140937620⟩,
⟨64,316021949,316022137⟩]
theorem checked40531 : checkPrefixCuts (2^48) 5316411393 10 Manual.Count131072.C040531.packed 64 cuts40531 = true := by
 decide +kernel
def pointBounds40531 : List (Nat × Nat × Nat) := [(5316470784,109032059968069,109032445572078)]
theorem point_links_checked40531 : (cuts40531.take 1).map (fun c => (5316411393-1+2*2^10*c.k,109031919030535+c.lower,109032304634458+c.upper)) = pointBounds40531 := by
 decide +kernel
def cuts40532 : List PrefixCut := [⟨47,222465419,222465552⟩,
⟨64,305160970,305161151⟩]
theorem checked40532 : checkPrefixCuts (2^48) 5316542465 10 Manual.Count131072.C040532.packed 64 cuts40532 = true := by
 decide +kernel
def pointBounds40532 : List (Nat × Nat × Nat) := [(5316638720,109032457517903,109032843122147)]
theorem point_links_checked40532 : (cuts40532.take 1).map (fun c => (5316542465-1+2*2^10*c.k,109032235052484+c.lower,109032620656595+c.upper)) = pointBounds40532 := by
 decide +kernel
def cuts40533 : List PrefixCut := [⟨64,310024032,310024219⟩]
theorem checked40533 : checkPrefixCuts (2^48) 5316673537 10 Manual.Count131072.C040533.packed 64 cuts40533 = true := by
 decide +kernel
def cuts40534 : List PrefixCut := [⟨1,4658773,4658776⟩,
⟨64,313563363,313563547⟩]
theorem checked40534 : checkPrefixCuts (2^48) 5316804609 10 Manual.Count131072.C040534.packed 64 cuts40534 = true := by
 decide +kernel
def pointBounds40534 : List (Nat × Nat × Nat) := [(5316806656,109032854896259,109033240500741)]
theorem point_links_checked40534 : (cuts40534.take 1).map (fun c => (5316804609-1+2*2^10*c.k,109032850237486+c.lower,109033235841965+c.upper)) = pointBounds40534 := by
 decide +kernel
def cuts40535 : List PrefixCut := [⟨19,92537572,92537627⟩,
⟨64,310485211,310485395⟩]
theorem checked40535 : checkPrefixCuts (2^48) 5316935681 10 Manual.Count131072.C040535.packed 64 cuts40535 = true := by
 decide +kernel
def pointBounds40535 : List (Nat × Nat × Nat) := [(5316974592,109033256338421,109033641943139)]
theorem point_links_checked40535 : (cuts40535.take 1).map (fun c => (5316935681-1+2*2^10*c.k,109033163800849+c.lower,109033549405512+c.upper)) = pointBounds40535 := by
 decide +kernel
def cuts40536 : List PrefixCut := [⟨37,180729059,180729168⟩,
⟨64,310901077,310901261⟩]
theorem checked40536 : checkPrefixCuts (2^48) 5317066753 10 Manual.Count131072.C040536.packed 64 cuts40536 = true := by
 decide +kernel
def pointBounds40536 : List (Nat × Nat × Nat) := [(5317142528,109033655015119,109034040620075)]
theorem point_links_checked40536 : (cuts40536.take 1).map (fun c => (5317066753-1+2*2^10*c.k,109033474286060+c.lower,109033859890907+c.upper)) = pointBounds40536 := by
 decide +kernel
def cuts40537 : List PrefixCut := [⟨55,269868430,269868591⟩,
⟨64,312746173,312746361⟩]
theorem checked40537 : checkPrefixCuts (2^48) 5317197825 10 Manual.Count131072.C040537.packed 64 cuts40537 = true := by
 decide +kernel
def pointBounds40537 : List (Nat × Nat × Nat) := [(5317310464,109034055055567,109034440660759)]
theorem point_links_checked40537 : (cuts40537.take 1).map (fun c => (5317197825-1+2*2^10*c.k,109033785187137+c.lower,109034170792168+c.upper)) = pointBounds40537 := by
 decide +kernel
def cuts40538 : List PrefixCut := [⟨64,312050296,312050477⟩]
theorem checked40538 : checkPrefixCuts (2^48) 5317328897 10 Manual.Count131072.C040538.packed 64 cuts40538 = true := by
 decide +kernel
def cuts40539 : List PrefixCut := [⟨9,43300009,43300034⟩,
⟨64,305584724,305584906⟩]
theorem checked40539 : checkPrefixCuts (2^48) 5317459969 10 Manual.Count131072.C040539.packed 64 cuts40539 = true := by
 decide +kernel
def pointBounds40539 : List (Nat × Nat × Nat) := [(5317478400,109034453283615,109034838889040)]
theorem point_links_checked40539 : (cuts40539.take 1).map (fun c => (5317459969-1+2*2^10*c.k,109034409983606+c.lower,109034795589006+c.upper)) = pointBounds40539 := by
 decide +kernel
def cuts40540 : List PrefixCut := [⟨27,131060892,131060967⟩,
⟨64,310076416,310076599⟩]
theorem checked40540 : checkPrefixCuts (2^48) 5317591041 10 Manual.Count131072.C040540.packed 64 cuts40540 = true := by
 decide +kernel
def pointBounds40540 : List (Nat × Nat × Nat) := [(5317646336,109034846629222,109035232234879)]
theorem point_links_checked40540 : (cuts40540.take 1).map (fun c => (5317591041-1+2*2^10*c.k,109034715568330+c.lower,109035101173912+c.upper)) = pointBounds40540 := by
 decide +kernel
def cuts40541 : List PrefixCut := [⟨45,214952864,214952988⟩,
⟨64,307104637,307104815⟩]
theorem checked40541 : checkPrefixCuts (2^48) 5317722113 10 Manual.Count131072.C040541.packed 64 cuts40541 = true := by
 decide +kernel
def pointBounds40541 : List (Nat × Nat × Nat) := [(5317814272,109035240597610,109035626203499)]
theorem point_links_checked40541 : (cuts40541.take 1).map (fun c => (5317722113-1+2*2^10*c.k,109035025644746+c.lower,109035411250511+c.upper)) = pointBounds40541 := by
 decide +kernel
def cuts40542 : List PrefixCut := [⟨63,296617091,296617271⟩,
⟨64,301592406,301592589⟩]
theorem checked40542 : checkPrefixCuts (2^48) 5317853185 10 Manual.Count131072.C040542.packed 64 cuts40542 = true := by
 decide +kernel
def pointBounds40542 : List (Nat × Nat × Nat) := [(5317982208,109035629366474,109036014972597)]
theorem point_links_checked40542 : (cuts40542.take 1).map (fun c => (5317853185-1+2*2^10*c.k,109035332749383+c.lower,109035718355326+c.upper)) = pointBounds40542 := by
 decide +kernel
def cuts40543 : List PrefixCut := [⟨64,308941991,308942173⟩]
theorem checked40543 : checkPrefixCuts (2^48) 5317984257 10 Manual.Count131072.C040543.packed 64 cuts40543 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S5.B000016
