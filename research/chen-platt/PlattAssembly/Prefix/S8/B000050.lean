import PlattAssemblyKernel
import PlattCertificates.Count131072.C071600
import PlattCertificates.Count131072.C071601
import PlattCertificates.Count131072.C071602
import PlattCertificates.Count131072.C071603
import PlattCertificates.Count131072.C071604
import PlattCertificates.Count131072.C071605
import PlattCertificates.Count131072.C071606
import PlattCertificates.Count131072.C071607
import PlattCertificates.Count131072.C071608
import PlattCertificates.Count131072.C071609
import PlattCertificates.Count131072.C071610
import PlattCertificates.Count131072.C071611
import PlattCertificates.Count131072.C071612
import PlattCertificates.Count131072.C071613
import PlattCertificates.Count131072.C071614
import PlattCertificates.Count131072.C071615
import PlattCertificates.Count131072.C071616
import PlattCertificates.Count131072.C071617
import PlattCertificates.Count131072.C071618
import PlattCertificates.Count131072.C071619
import PlattCertificates.Count131072.C071620
import PlattCertificates.Count131072.C071621
import PlattCertificates.Count131072.C071622
import PlattCertificates.Count131072.C071623
import PlattCertificates.Count131072.C071624
import PlattCertificates.Count131072.C071625
import PlattCertificates.Count131072.C071626
import PlattCertificates.Count131072.C071627
import PlattCertificates.Count131072.C071628
import PlattCertificates.Count131072.C071629
import PlattCertificates.Count131072.C071630
import PlattCertificates.Count131072.C071631
namespace ChenEffective.PlattWindow.Assembly.Prefix.S8.B000050
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts71600 : List PrefixCut := [⟨64,170616235,170616335⟩]
theorem checked71600 : checkPrefixCuts (2^48) 9388687361 10 Manual.Count131072.C071600.packed 64 cuts71600 = true := by
 decide +kernel
def cuts71601 : List PrefixCut := [⟨14,37414733,37414753⟩,
⟨64,170344021,170344124⟩]
theorem checked71601 : checkPrefixCuts (2^48) 9388818433 10 Manual.Count131072.C071601.packed 64 cuts71601 = true := by
 decide +kernel
def pointBounds71601 : List (Nat × Nat × Nat) := [(9388847104,116090999303281,116091388972127)]
theorem point_links_checked71601 : (cuts71601.take 1).map (fun c => (9388818433-1+2*2^10*c.k,116090961888548+c.lower,116091351557374+c.upper)) = pointBounds71601 := by
 decide +kernel
def cuts71602 : List PrefixCut := [⟨64,171720694,171720795⟩]
theorem checked71602 : checkPrefixCuts (2^48) 9388949505 10 Manual.Count131072.C071602.packed 64 cuts71602 = true := by
 decide +kernel
def cuts71603 : List PrefixCut := [⟨30,80882976,80883022⟩,
⟨64,171388542,171388645⟩]
theorem checked71603 : checkPrefixCuts (2^48) 9389080577 10 Manual.Count131072.C071603.packed 64 cuts71603 = true := by
 decide +kernel
def pointBounds71603 : List (Nat × Nat × Nat) := [(9389142016,116091384836239,116091774505315)]
theorem point_links_checked71603 : (cuts71603.take 1).map (fun c => (9389080577-1+2*2^10*c.k,116091303953263+c.lower,116091693622293+c.upper)) = pointBounds71603 := by
 decide +kernel
def cuts71604 : List PrefixCut := [⟨64,170816534,170816644⟩]
theorem checked71604 : checkPrefixCuts (2^48) 9389211649 10 Manual.Count131072.C071604.packed 64 cuts71604 = true := by
 decide +kernel
def cuts71605 : List PrefixCut := [⟨46,125277962,125278035⟩,
⟨64,172313073,172313177⟩]
theorem checked71605 : checkPrefixCuts (2^48) 9389342721 10 Manual.Count131072.C071605.packed 64 cuts71605 = true := by
 decide +kernel
def pointBounds71605 : List (Nat × Nat × Nat) := [(9389436928,116091771436301,116092161105617)]
theorem point_links_checked71605 : (cuts71605.take 1).map (fun c => (9389342721-1+2*2^10*c.k,116091646158339+c.lower,116092035827582+c.upper)) = pointBounds71605 := by
 decide +kernel
def cuts71606 : List PrefixCut := [⟨64,169163016,169163116⟩]
theorem checked71606 : checkPrefixCuts (2^48) 9389473793 10 Manual.Count131072.C071606.packed 64 cuts71606 = true := by
 decide +kernel
def cuts71607 : List PrefixCut := [⟨62,164754068,164754169⟩,
⟨64,170299790,170299895⟩]
theorem checked71607 : checkPrefixCuts (2^48) 9389604865 10 Manual.Count131072.C071607.packed 64 cuts71607 = true := by
 decide +kernel
def pointBounds71607 : List (Nat × Nat × Nat) := [(9389731840,116092152388496,116092542058044)]
theorem point_links_checked71607 : (cuts71607.take 1).map (fun c => (9389604865-1+2*2^10*c.k,116091987634428+c.lower,116092377303875+c.upper)) = pointBounds71607 := by
 decide +kernel
def cuts71608 : List PrefixCut := [⟨64,172185938,172186038⟩]
theorem checked71608 : checkPrefixCuts (2^48) 9389735937 10 Manual.Count131072.C071608.packed 64 cuts71608 = true := by
 decide +kernel
def cuts71609 : List PrefixCut := [⟨64,172123588,172123691⟩]
theorem checked71609 : checkPrefixCuts (2^48) 9389867009 10 Manual.Count131072.C071609.packed 64 cuts71609 = true := by
 decide +kernel
def cuts71610 : List PrefixCut := [⟨14,38399241,38399263⟩,
⟨64,172780652,172780751⟩]
theorem checked71610 : checkPrefixCuts (2^48) 9389998081 10 Manual.Count131072.C071610.packed 64 cuts71610 = true := by
 decide +kernel
def pointBounds71610 : List (Nat × Nat × Nat) := [(9390026752,116092540642985,116092930312762)]
theorem point_links_checked71610 : (cuts71610.take 1).map (fun c => (9389998081-1+2*2^10*c.k,116092502243744+c.lower,116092891913499+c.upper)) = pointBounds71610 := by
 decide +kernel
def cuts71611 : List PrefixCut := [⟨64,170979718,170979818⟩]
theorem checked71611 : checkPrefixCuts (2^48) 9390129153 10 Manual.Count131072.C071611.packed 64 cuts71611 = true := by
 decide +kernel
def cuts71612 : List PrefixCut := [⟨30,80543090,80543135⟩,
⟨64,172206305,172206403⟩]
theorem checked71612 : checkPrefixCuts (2^48) 9390260225 10 Manual.Count131072.C071612.packed 64 cuts71612 = true := by
 decide +kernel
def pointBounds71612 : List (Nat × Nat × Nat) := [(9390321664,116092926547204,116093316217203)]
theorem point_links_checked71612 : (cuts71612.take 1).map (fun c => (9390260225-1+2*2^10*c.k,116092846004114+c.lower,116093235674068+c.upper)) = pointBounds71612 := by
 decide +kernel
def cuts71613 : List PrefixCut := [⟨64,171934127,171934225⟩]
theorem checked71613 : checkPrefixCuts (2^48) 9390391297 10 Manual.Count131072.C071613.packed 64 cuts71613 = true := by
 decide +kernel
def cuts71614 : List PrefixCut := [⟨46,121575394,121575459⟩,
⟨64,171092440,171092536⟩]
theorem checked71614 : checkPrefixCuts (2^48) 9390522369 10 Manual.Count131072.C071614.packed 64 cuts71614 = true := by
 decide +kernel
def pointBounds71614 : List (Nat × Nat × Nat) := [(9390616576,116093311719940,116093701390155)]
theorem point_links_checked71614 : (cuts71614.take 1).map (fun c => (9390522369-1+2*2^10*c.k,116093190144546+c.lower,116093579814696+c.upper)) = pointBounds71614 := by
 decide +kernel
def cuts71615 : List PrefixCut := [⟨64,170220829,170220931⟩]
theorem checked71615 : checkPrefixCuts (2^48) 9390653441 10 Manual.Count131072.C071615.packed 64 cuts71615 = true := by
 decide +kernel
def cuts71616 : List PrefixCut := [⟨62,166112136,166112239⟩,
⟨64,171027726,171027832⟩]
theorem checked71616 : checkPrefixCuts (2^48) 9390784513 10 Manual.Count131072.C071616.packed 64 cuts71616 = true := by
 decide +kernel
def pointBounds71616 : List (Nat × Nat × Nat) := [(9390911488,116093697569951,116094087240402)]
theorem point_links_checked71616 : (cuts71616.take 1).map (fun c => (9390784513-1+2*2^10*c.k,116093531457815+c.lower,116093921128163+c.upper)) = pointBounds71616 := by
 decide +kernel
def cuts71617 : List PrefixCut := [⟨64,169196992,169197093⟩]
theorem checked71617 : checkPrefixCuts (2^48) 9390915585 10 Manual.Count131072.C071617.packed 64 cuts71617 = true := by
 decide +kernel
def cuts71618 : List PrefixCut := [⟨64,171112875,171112978⟩]
theorem checked71618 : checkPrefixCuts (2^48) 9391046657 10 Manual.Count131072.C071618.packed 64 cuts71618 = true := by
 decide +kernel
def cuts71619 : List PrefixCut := [⟨14,37884889,37884911⟩,
⟨64,172579113,172579214⟩]
theorem checked71619 : checkPrefixCuts (2^48) 9391177729 10 Manual.Count131072.C071619.packed 64 cuts71619 = true := by
 decide +kernel
def pointBounds71619 : List (Nat × Nat × Nat) := [(9391206400,116094080680297,116094470350977)]
theorem point_links_checked71619 : (cuts71619.take 1).map (fun c => (9391177729-1+2*2^10*c.k,116094042795408+c.lower,116094432466066+c.upper)) = pointBounds71619 := by
 decide +kernel
def cuts71620 : List PrefixCut := [⟨64,171737503,171737603⟩]
theorem checked71620 : checkPrefixCuts (2^48) 9391308801 10 Manual.Count131072.C071620.packed 64 cuts71620 = true := by
 decide +kernel
def cuts71621 : List PrefixCut := [⟨30,78824606,78824654⟩,
⟨64,170236537,170236640⟩]
theorem checked71621 : checkPrefixCuts (2^48) 9391439873 10 Manual.Count131072.C071621.packed 64 cuts71621 = true := by
 decide +kernel
def pointBounds71621 : List (Nat × Nat × Nat) := [(9391501312,116094465936630,116094855607537)]
theorem point_links_checked71621 : (cuts71621.take 1).map (fun c => (9391439873-1+2*2^10*c.k,116094387112024+c.lower,116094776782883+c.upper)) = pointBounds71621 := by
 decide +kernel
def cuts71622 : List PrefixCut := [⟨64,170503898,170504000⟩]
theorem checked71622 : checkPrefixCuts (2^48) 9391570945 10 Manual.Count131072.C071622.packed 64 cuts71622 = true := by
 decide +kernel
def cuts71623 : List PrefixCut := [⟨46,124856870,124856946⟩,
⟨64,173138917,173139024⟩]
theorem checked71623 : checkPrefixCuts (2^48) 9391702017 10 Manual.Count131072.C071623.packed 64 cuts71623 = true := by
 decide +kernel
def pointBounds71623 : List (Nat × Nat × Nat) := [(9391796224,116094852709329,116095242380469)]
theorem point_links_checked71623 : (cuts71623.take 1).map (fun c => (9391702017-1+2*2^10*c.k,116094727852459+c.lower,116095117523523+c.upper)) = pointBounds71623 := by
 decide +kernel
def cuts71624 : List PrefixCut := [⟨64,169989660,169989765⟩]
theorem checked71624 : checkPrefixCuts (2^48) 9391833089 10 Manual.Count131072.C071624.packed 64 cuts71624 = true := by
 decide +kernel
def cuts71625 : List PrefixCut := [⟨62,164442959,164443053⟩,
⟨64,170047227,170047324⟩]
theorem checked71625 : checkPrefixCuts (2^48) 9391964161 10 Manual.Count131072.C071625.packed 64 cuts71625 = true := by
 decide +kernel
def pointBounds71625 : List (Nat × Nat × Nat) := [(9392091136,116095235423995,116095625095365)]
theorem point_links_checked71625 : (cuts71625.take 1).map (fun c => (9391964161-1+2*2^10*c.k,116095070981036+c.lower,116095460652312+c.upper)) = pointBounds71625 := by
 decide +kernel
def cuts71626 : List PrefixCut := [⟨64,171513343,171513444⟩]
theorem checked71626 : checkPrefixCuts (2^48) 9392095233 10 Manual.Count131072.C071626.packed 64 cuts71626 = true := by
 decide +kernel
def cuts71627 : List PrefixCut := [⟨64,172140284,172140387⟩]
theorem checked71627 : checkPrefixCuts (2^48) 9392226305 10 Manual.Count131072.C071627.packed 64 cuts71627 = true := by
 decide +kernel
def cuts71628 : List PrefixCut := [⟨14,38629343,38629365⟩,
⟨64,173036934,173037039⟩]
theorem checked71628 : checkPrefixCuts (2^48) 9392357377 10 Manual.Count131072.C071628.packed 64 cuts71628 = true := by
 decide +kernel
def pointBounds71628 : List (Nat × Nat × Nat) := [(9392386048,116095623311233,116096012982832)]
theorem point_links_checked71628 : (cuts71628.take 1).map (fun c => (9392357377-1+2*2^10*c.k,116095584681890+c.lower,116095974353467+c.upper)) = pointBounds71628 := by
 decide +kernel
def cuts71629 : List PrefixCut := [⟨64,170996709,170996808⟩]
theorem checked71629 : checkPrefixCuts (2^48) 9392488449 10 Manual.Count131072.C071629.packed 64 cuts71629 = true := by
 decide +kernel
def cuts71630 : List PrefixCut := [⟨30,79294188,79294231⟩,
⟨64,169226238,169226333⟩]
theorem checked71630 : checkPrefixCuts (2^48) 9392619521 10 Manual.Count131072.C071630.packed 64 cuts71630 = true := by
 decide +kernel
def pointBounds71630 : List (Nat × Nat × Nat) := [(9392680960,116096008009721,116096397681545)]
theorem point_links_checked71630 : (cuts71630.take 1).map (fun c => (9392619521-1+2*2^10*c.k,116095928715533+c.lower,116096318387314+c.upper)) = pointBounds71630 := by
 decide +kernel
def cuts71631 : List PrefixCut := [⟨64,169583480,169583579⟩]
theorem checked71631 : checkPrefixCuts (2^48) 9392750593 10 Manual.Count131072.C071631.packed 64 cuts71631 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S8.B000050
