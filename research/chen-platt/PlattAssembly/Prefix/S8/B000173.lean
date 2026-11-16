import PlattAssemblyKernel
import PlattCertificates.Count131072.C075536
import PlattCertificates.Count131072.C075537
import PlattCertificates.Count131072.C075538
import PlattCertificates.Count131072.C075539
import PlattCertificates.Count131072.C075540
import PlattCertificates.Count131072.C075541
import PlattCertificates.Count131072.C075542
import PlattCertificates.Count131072.C075543
import PlattCertificates.Count131072.C075544
import PlattCertificates.Count131072.C075545
import PlattCertificates.Count131072.C075546
import PlattCertificates.Count131072.C075547
import PlattCertificates.Count131072.C075548
import PlattCertificates.Count131072.C075549
import PlattCertificates.Count131072.C075550
import PlattCertificates.Count131072.C075551
import PlattCertificates.Count131072.C075552
import PlattCertificates.Count131072.C075553
import PlattCertificates.Count131072.C075554
import PlattCertificates.Count131072.C075555
import PlattCertificates.Count131072.C075556
import PlattCertificates.Count131072.C075557
import PlattCertificates.Count131072.C075558
import PlattCertificates.Count131072.C075559
import PlattCertificates.Count131072.C075560
import PlattCertificates.Count131072.C075561
import PlattCertificates.Count131072.C075562
import PlattCertificates.Count131072.C075563
import PlattCertificates.Count131072.C075564
import PlattCertificates.Count131072.C075565
import PlattCertificates.Count131072.C075566
import PlattCertificates.Count131072.C075567
namespace ChenEffective.PlattWindow.Assembly.Prefix.S8.B000173
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts75536 : List PrefixCut := [⟨64,161843091,161843188⟩]
theorem checked75536 : checkPrefixCuts (2^48) 9904586753 10 Manual.Count131072.C075536.packed 64 cuts75536 = true := by
 decide +kernel
def cuts75537 : List PrefixCut := [⟨11,28162468,28162484⟩,
⟨64,162039867,162039963⟩]
theorem checked75537 : checkPrefixCuts (2^48) 9904717825 10 Manual.Count131072.C075537.packed 64 cuts75537 = true := by
 decide +kernel
def pointBounds75537 : List (Nat × Nat × Nat) := [(9904740352,116745976453525,116746366513338)]
theorem point_links_checked75537 : (cuts75537.take 1).map (fun c => (9904717825-1+2*2^10*c.k,116745948291057+c.lower,116746338350854+c.upper)) = pointBounds75537 := by
 decide +kernel
def cuts75538 : List PrefixCut := [⟨64,160531589,160531690⟩]
theorem checked75538 : checkPrefixCuts (2^48) 9904848897 10 Manual.Count131072.C075538.packed 64 cuts75538 = true := by
 decide +kernel
def cuts75539 : List PrefixCut := [⟨35,89742180,89742234⟩,
⟨64,164507888,164507990⟩]
theorem checked75539 : checkPrefixCuts (2^48) 9904979969 10 Manual.Count131072.C075539.packed 64 cuts75539 = true := by
 decide +kernel
def pointBounds75539 : List (Nat × Nat × Nat) := [(9905051648,116746360604693,116746750664741)]
theorem point_links_checked75539 : (cuts75539.take 1).map (fun c => (9904979969-1+2*2^10*c.k,116746270862513+c.lower,116746660922507+c.upper)) = pointBounds75539 := by
 decide +kernel
def cuts75540 : List PrefixCut := [⟨64,159987414,159987512⟩]
theorem checked75540 : checkPrefixCuts (2^48) 9905111041 10 Manual.Count131072.C075540.packed 64 cuts75540 = true := by
 decide +kernel
def cuts75541 : List PrefixCut := [⟨59,149897496,149897585⟩,
⟨64,162656460,162656556⟩]
theorem checked75541 : checkPrefixCuts (2^48) 9905242113 10 Manual.Count131072.C075541.packed 64 cuts75541 = true := by
 decide +kernel
def pointBounds75541 : List (Nat × Nat × Nat) := [(9905362944,116746745255311,116747135315594)]
theorem point_links_checked75541 : (cuts75541.take 1).map (fun c => (9905242113-1+2*2^10*c.k,116746595357815+c.lower,116746985418009+c.upper)) = pointBounds75541 := by
 decide +kernel
def cuts75542 : List PrefixCut := [⟨64,160636764,160636854⟩]
theorem checked75542 : checkPrefixCuts (2^48) 9905373185 10 Manual.Count131072.C075542.packed 64 cuts75542 = true := by
 decide +kernel
def cuts75543 : List PrefixCut := [⟨64,160492551,160492645⟩]
theorem checked75543 : checkPrefixCuts (2^48) 9905504257 10 Manual.Count131072.C075543.packed 64 cuts75543 = true := by
 decide +kernel
def cuts75544 : List PrefixCut := [⟨19,47624506,47624534⟩,
⟨64,163786617,163786710⟩]
theorem checked75544 : checkPrefixCuts (2^48) 9905635329 10 Manual.Count131072.C075544.packed 64 cuts75544 = true := by
 decide +kernel
def pointBounds75544 : List (Nat × Nat × Nat) := [(9905674240,116747126768096,116747516828598)]
theorem point_links_checked75544 : (cuts75544.take 1).map (fun c => (9905635329-1+2*2^10*c.k,116747079143590+c.lower,116747469204064+c.upper)) = pointBounds75544 := by
 decide +kernel
def cuts75545 : List PrefixCut := [⟨64,162107971,162108078⟩]
theorem checked75545 : checkPrefixCuts (2^48) 9905766401 10 Manual.Count131072.C075545.packed 64 cuts75545 = true := by
 decide +kernel
def cuts75546 : List PrefixCut := [⟨43,109709370,109709432⟩,
⟨64,161622784,161622876⟩]
theorem checked75546 : checkPrefixCuts (2^48) 9905897473 10 Manual.Count131072.C075546.packed 64 cuts75546 = true := by
 decide +kernel
def pointBounds75546 : List (Nat × Nat × Nat) := [(9905985536,116747514747548,116747904808284)]
theorem point_links_checked75546 : (cuts75546.take 1).map (fun c => (9905897473-1+2*2^10*c.k,116747405038178+c.lower,116747795098852+c.upper)) = pointBounds75546 := by
 decide +kernel
def cuts75547 : List PrefixCut := [⟨64,161052350,161052447⟩]
theorem checked75547 : checkPrefixCuts (2^48) 9906028545 10 Manual.Count131072.C075547.packed 64 cuts75547 = true := by
 decide +kernel
def cuts75548 : List PrefixCut := [⟨64,163664303,163664407⟩]
theorem checked75548 : checkPrefixCuts (2^48) 9906159617 10 Manual.Count131072.C075548.packed 64 cuts75548 = true := by
 decide +kernel
def cuts75549 : List PrefixCut := [⟨3,7756952,7756956⟩,
⟨64,162184614,162184708⟩]
theorem checked75549 : checkPrefixCuts (2^48) 9906290689 10 Manual.Count131072.C075549.packed 64 cuts75549 = true := by
 decide +kernel
def pointBounds75549 : List (Nat × Nat × Nat) := [(9906296832,116747899134567,116748289195538)]
theorem point_links_checked75549 : (cuts75549.take 1).map (fun c => (9906290689-1+2*2^10*c.k,116747891377615+c.lower,116748281438582+c.upper)) = pointBounds75549 := by
 decide +kernel
def cuts75550 : List PrefixCut := [⟨64,161244843,161244944⟩]
theorem checked75550 : checkPrefixCuts (2^48) 9906421761 10 Manual.Count131072.C075550.packed 64 cuts75550 = true := by
 decide +kernel
def cuts75551 : List PrefixCut := [⟨27,68730860,68730899⟩,
⟨64,163373675,163373771⟩]
theorem checked75551 : checkPrefixCuts (2^48) 9906552833 10 Manual.Count131072.C075551.packed 64 cuts75551 = true := by
 decide +kernel
def pointBounds75551 : List (Nat × Nat × Nat) := [(9906608128,116748283537932,116748673599133)]
theorem point_links_checked75551 : (cuts75551.take 1).map (fun c => (9906552833-1+2*2^10*c.k,116748214807072+c.lower,116748604868234+c.upper)) = pointBounds75551 := by
 decide +kernel
def cuts75552 : List PrefixCut := [⟨64,161922472,161922571⟩]
theorem checked75552 : checkPrefixCuts (2^48) 9906683905 10 Manual.Count131072.C075552.packed 64 cuts75552 = true := by
 decide +kernel
def cuts75553 : List PrefixCut := [⟨51,127712396,127712471⟩,
⟨64,159192793,159192887⟩]
theorem checked75553 : checkPrefixCuts (2^48) 9906814977 10 Manual.Count131072.C075553.packed 64 cuts75553 = true := by
 decide +kernel
def pointBounds75553 : List (Nat × Nat × Nat) := [(9906919424,116748667815615,116749057877047)]
theorem point_links_checked75553 : (cuts75553.take 1).map (fun c => (9906814977-1+2*2^10*c.k,116748540103219+c.lower,116748930164576+c.upper)) = pointBounds75553 := by
 decide +kernel
def cuts75554 : List PrefixCut := [⟨64,164929842,164929940⟩]
theorem checked75554 : checkPrefixCuts (2^48) 9906946049 10 Manual.Count131072.C075554.packed 64 cuts75554 = true := by
 decide +kernel
def cuts75555 : List PrefixCut := [⟨64,161802402,161802493⟩]
theorem checked75555 : checkPrefixCuts (2^48) 9907077121 10 Manual.Count131072.C075555.packed 64 cuts75555 = true := by
 decide +kernel
def cuts75556 : List PrefixCut := [⟨11,27473524,27473537⟩,
⟨64,161203635,161203729⟩]
theorem checked75556 : checkPrefixCuts (2^48) 9907208193 10 Manual.Count131072.C075556.packed 64 cuts75556 = true := by
 decide +kernel
def pointBounds75556 : List (Nat × Nat × Nat) := [(9907230720,116749053501780,116749443563433)]
theorem point_links_checked75556 : (cuts75556.take 1).map (fun c => (9907208193-1+2*2^10*c.k,116749026028256+c.lower,116749416089896+c.upper)) = pointBounds75556 := by
 decide +kernel
def cuts75557 : List PrefixCut := [⟨64,161854954,161855049⟩]
theorem checked75557 : checkPrefixCuts (2^48) 9907339265 10 Manual.Count131072.C075557.packed 64 cuts75557 = true := by
 decide +kernel
def cuts75558 : List PrefixCut := [⟨35,90458288,90458342⟩,
⟨64,162676704,162676808⟩]
theorem checked75558 : checkPrefixCuts (2^48) 9907470337 10 Manual.Count131072.C075558.packed 64 cuts75558 = true := by
 decide +kernel
def pointBounds75558 : List (Nat × Nat × Nat) := [(9907542016,116749439545133,116749829607016)]
theorem point_links_checked75558 : (cuts75558.take 1).map (fun c => (9907470337-1+2*2^10*c.k,116749349086845+c.lower,116749739148674+c.upper)) = pointBounds75558 := by
 decide +kernel
def cuts75559 : List PrefixCut := [⟨64,162504085,162504176⟩]
theorem checked75559 : checkPrefixCuts (2^48) 9907601409 10 Manual.Count131072.C075559.packed 64 cuts75559 = true := by
 decide +kernel
def cuts75560 : List PrefixCut := [⟨59,147331378,147331466⟩,
⟨64,160143953,160144048⟩]
theorem checked75560 : checkPrefixCuts (2^48) 9907732481 10 Manual.Count131072.C075560.packed 64 cuts75560 = true := by
 decide +kernel
def pointBounds75560 : List (Nat × Nat × Nat) := [(9907853312,116749821599012,116750211661124)]
theorem point_links_checked75560 : (cuts75560.take 1).map (fun c => (9907732481-1+2*2^10*c.k,116749674267634+c.lower,116750064329658+c.upper)) = pointBounds75560 := by
 decide +kernel
def cuts75561 : List PrefixCut := [⟨64,161704335,161704429⟩]
theorem checked75561 : checkPrefixCuts (2^48) 9907863553 10 Manual.Count131072.C075561.packed 64 cuts75561 = true := by
 decide +kernel
def cuts75562 : List PrefixCut := [⟨64,160821525,160821620⟩]
theorem checked75562 : checkPrefixCuts (2^48) 9907994625 10 Manual.Count131072.C075562.packed 64 cuts75562 = true := by
 decide +kernel
def cuts75563 : List PrefixCut := [⟨19,47442084,47442113⟩,
⟨64,159427393,159427494⟩]
theorem checked75563 : checkPrefixCuts (2^48) 9908125697 10 Manual.Count131072.C075563.packed 64 cuts75563 = true := by
 decide +kernel
def pointBounds75563 : List (Nat × Nat × Nat) := [(9908164608,116750204379531,116750594441868)]
theorem point_links_checked75563 : (cuts75563.take 1).map (fun c => (9908125697-1+2*2^10*c.k,116750156937447+c.lower,116750546999755+c.upper)) = pointBounds75563 := by
 decide +kernel
def cuts75564 : List PrefixCut := [⟨64,162408112,162408212⟩]
theorem checked75564 : checkPrefixCuts (2^48) 9908256769 10 Manual.Count131072.C075564.packed 64 cuts75564 = true := by
 decide +kernel
def cuts75565 : List PrefixCut := [⟨43,108744342,108744411⟩,
⟨64,163627488,163627588⟩]
theorem checked75565 : checkPrefixCuts (2^48) 9908387841 10 Manual.Count131072.C075565.packed 64 cuts75565 = true := by
 decide +kernel
def pointBounds75565 : List (Nat × Nat × Nat) := [(9908475904,116750587517294,116750977579872)]
theorem point_links_checked75565 : (cuts75565.take 1).map (fun c => (9908387841-1+2*2^10*c.k,116750478772952+c.lower,116750868835461+c.upper)) = pointBounds75565 := by
 decide +kernel
def cuts75566 : List PrefixCut := [⟨64,161153895,161153998⟩]
theorem checked75566 : checkPrefixCuts (2^48) 9908518913 10 Manual.Count131072.C075566.packed 64 cuts75566 = true := by
 decide +kernel
def cuts75567 : List PrefixCut := [⟨64,161208585,161208687⟩]
theorem checked75567 : checkPrefixCuts (2^48) 9908649985 10 Manual.Count131072.C075567.packed 64 cuts75567 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S8.B000173
