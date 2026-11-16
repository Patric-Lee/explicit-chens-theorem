import PlattAssemblyKernel
import PlattCertificates.Count131072.C057520
import PlattCertificates.Count131072.C057521
import PlattCertificates.Count131072.C057522
import PlattCertificates.Count131072.C057523
import PlattCertificates.Count131072.C057524
import PlattCertificates.Count131072.C057525
import PlattCertificates.Count131072.C057526
import PlattCertificates.Count131072.C057527
import PlattCertificates.Count131072.C057528
import PlattCertificates.Count131072.C057529
import PlattCertificates.Count131072.C057530
import PlattCertificates.Count131072.C057531
import PlattCertificates.Count131072.C057532
import PlattCertificates.Count131072.C057533
import PlattCertificates.Count131072.C057534
import PlattCertificates.Count131072.C057535
import PlattCertificates.Count131072.C057536
import PlattCertificates.Count131072.C057537
import PlattCertificates.Count131072.C057538
import PlattCertificates.Count131072.C057539
import PlattCertificates.Count131072.C057540
import PlattCertificates.Count131072.C057541
import PlattCertificates.Count131072.C057542
import PlattCertificates.Count131072.C057543
import PlattCertificates.Count131072.C057544
import PlattCertificates.Count131072.C057545
import PlattCertificates.Count131072.C057546
import PlattCertificates.Count131072.C057547
import PlattCertificates.Count131072.C057548
import PlattCertificates.Count131072.C057549
import PlattCertificates.Count131072.C057550
import PlattCertificates.Count131072.C057551
namespace ChenEffective.PlattWindow.Assembly.Prefix.S6.B000235
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts57520 : List PrefixCut := [⟨64,213328485,213328605⟩]
theorem checked57520 : checkPrefixCuts (2^48) 7543193601 10 Manual.Count131072.C057520.packed 64 cuts57520 = true := by
 decide +kernel
def cuts57521 : List PrefixCut := [⟨40,132167010,132167089⟩,
⟨64,215078516,215078640⟩]
theorem checked57521 : checkPrefixCuts (2^48) 7543324673 10 Manual.Count131072.C057521.packed 64 cuts57521 = true := by
 decide +kernel
def pointBounds57521 : List (Nat × Nat × Nat) := [(7543406592,113395523974241,113395912084112)]
theorem point_links_checked57521 : (cuts57521.take 1).map (fun c => (7543324673-1+2*2^10*c.k,113395391807231+c.lower,113395779917023+c.upper)) = pointBounds57521 := by
 decide +kernel
def cuts57522 : List PrefixCut := [⟨64,213059882,213060006⟩]
theorem checked57522 : checkPrefixCuts (2^48) 7543455745 10 Manual.Count131072.C057522.packed 64 cuts57522 = true := by
 decide +kernel
def cuts57523 : List PrefixCut := [⟨28,94476509,94476561⟩,
⟨64,214362123,214362242⟩]
theorem checked57523 : checkPrefixCuts (2^48) 7543586817 10 Manual.Count131072.C057523.packed 64 cuts57523 = true := by
 decide +kernel
def pointBounds57523 : List (Nat × Nat × Nat) := [(7543644160,113395914422138,113396302532230)]
theorem point_links_checked57523 : (cuts57523.take 1).map (fun c => (7543586817-1+2*2^10*c.k,113395819945629+c.lower,113396208055669+c.upper)) = pointBounds57523 := by
 decide +kernel
def cuts57524 : List PrefixCut := [⟨64,215477753,215477874⟩]
theorem checked57524 : checkPrefixCuts (2^48) 7543717889 10 Manual.Count131072.C057524.packed 64 cuts57524 = true := by
 decide +kernel
def cuts57525 : List PrefixCut := [⟨16,54213987,54214019⟩,
⟨64,215660566,215660690⟩]
theorem checked57525 : checkPrefixCuts (2^48) 7543848961 10 Manual.Count131072.C057525.packed 64 cuts57525 = true := by
 decide +kernel
def pointBounds57525 : List (Nat × Nat × Nat) := [(7543881728,113396303999492,113396692109804)]
theorem point_links_checked57525 : (cuts57525.take 1).map (fun c => (7543848961-1+2*2^10*c.k,113396249785505+c.lower,113396637895785+c.upper)) = pointBounds57525 := by
 decide +kernel
def cuts57526 : List PrefixCut := [⟨64,211963058,211963176⟩]
theorem checked57526 : checkPrefixCuts (2^48) 7543980033 10 Manual.Count131072.C057526.packed 64 cuts57526 = true := by
 decide +kernel
def cuts57527 : List PrefixCut := [⟨4,14663036,14663044⟩,
⟨64,215690402,215690528⟩]
theorem checked57527 : checkPrefixCuts (2^48) 7544111105 10 Manual.Count131072.C057527.packed 64 cuts57527 = true := by
 decide +kernel
def pointBounds57527 : List (Nat × Nat × Nat) := [(7544119296,113396692072165,113397080182695)]
theorem point_links_checked57527 : (cuts57527.take 1).map (fun c => (7544111105-1+2*2^10*c.k,113396677409129+c.lower,113397065519651+c.upper)) = pointBounds57527 := by
 decide +kernel
def cuts57528 : List PrefixCut := [⟨56,189980547,189980651⟩,
⟨64,216320905,216321024⟩]
theorem checked57528 : checkPrefixCuts (2^48) 7544242177 10 Manual.Count131072.C057528.packed 64 cuts57528 = true := by
 decide +kernel
def pointBounds57528 : List (Nat × Nat × Nat) := [(7544356864,113397083080078,113397471190830)]
theorem point_links_checked57528 : (cuts57528.take 1).map (fun c => (7544242177-1+2*2^10*c.k,113396893099531+c.lower,113397281210179+c.upper)) = pointBounds57528 := by
 decide +kernel
def cuts57529 : List PrefixCut := [⟨64,216876773,216876895⟩]
theorem checked57529 : checkPrefixCuts (2^48) 7544373249 10 Manual.Count131072.C057529.packed 64 cuts57529 = true := by
 decide +kernel
def cuts57530 : List PrefixCut := [⟨44,149158896,149158982⟩,
⟨64,218178798,218178923⟩]
theorem checked57530 : checkPrefixCuts (2^48) 7544504321 10 Manual.Count131072.C057530.packed 64 cuts57530 = true := by
 decide +kernel
def pointBounds57530 : List (Nat × Nat × Nat) := [(7544594432,113397475456105,113397863567080)]
theorem point_links_checked57530 : (cuts57530.take 1).map (fun c => (7544504321-1+2*2^10*c.k,113397326297209+c.lower,113397714408098+c.upper)) = pointBounds57530 := by
 decide +kernel
def cuts57531 : List PrefixCut := [⟨64,213884633,213884756⟩]
theorem checked57531 : checkPrefixCuts (2^48) 7544635393 10 Manual.Count131072.C057531.packed 64 cuts57531 = true := by
 decide +kernel
def cuts57532 : List PrefixCut := [⟨32,107146102,107146162⟩,
⟨64,214888192,214888313⟩]
theorem checked57532 : checkPrefixCuts (2^48) 7544766465 10 Manual.Count131072.C057532.packed 64 cuts57532 = true := by
 decide +kernel
def pointBounds57532 : List (Nat × Nat × Nat) := [(7544832000,113397865506742,113398253617939)]
theorem point_links_checked57532 : (cuts57532.take 1).map (fun c => (7544766465-1+2*2^10*c.k,113397758360640+c.lower,113398146471777+c.upper)) = pointBounds57532 := by
 decide +kernel
def cuts57533 : List PrefixCut := [⟨64,215406771,215406893⟩]
theorem checked57533 : checkPrefixCuts (2^48) 7544897537 10 Manual.Count131072.C057533.packed 64 cuts57533 = true := by
 decide +kernel
def cuts57534 : List PrefixCut := [⟨20,65322642,65322679⟩,
⟨64,213761551,213761677⟩]
theorem checked57534 : checkPrefixCuts (2^48) 7545028609 10 Manual.Count131072.C057534.packed 64 cuts57534 = true := by
 decide +kernel
def pointBounds57534 : List (Nat × Nat × Nat) := [(7545069568,113398253978245,113398642089662)]
theorem point_links_checked57534 : (cuts57534.take 1).map (fun c => (7545028609-1+2*2^10*c.k,113398188655603+c.lower,113398576766983+c.upper)) = pointBounds57534 := by
 decide +kernel
def cuts57535 : List PrefixCut := [⟨64,217078019,217078137⟩]
theorem checked57535 : checkPrefixCuts (2^48) 7545159681 10 Manual.Count131072.C057535.packed 64 cuts57535 = true := by
 decide +kernel
def cuts57536 : List PrefixCut := [⟨8,26001356,26001369⟩,
⟨64,215656647,215656771⟩]
theorem checked57536 : checkPrefixCuts (2^48) 7545290753 10 Manual.Count131072.C057536.packed 64 cuts57536 = true := by
 decide +kernel
def pointBounds57536 : List (Nat × Nat × Nat) := [(7545307136,113398645496529,113399033608166)]
theorem point_links_checked57536 : (cuts57536.take 1).map (fun c => (7545290753-1+2*2^10*c.k,113398619495173+c.lower,113399007606797+c.upper)) = pointBounds57536 := by
 decide +kernel
def cuts57537 : List PrefixCut := [⟨60,203753123,203753238⟩,
⟨64,218413373,218413496⟩]
theorem checked57537 : checkPrefixCuts (2^48) 7545421825 10 Manual.Count131072.C057537.packed 64 cuts57537 = true := by
 decide +kernel
def pointBounds57537 : List (Nat × Nat × Nat) := [(7545544704,113399038904943,113399427016806)]
theorem point_links_checked57537 : (cuts57537.take 1).map (fun c => (7545421825-1+2*2^10*c.k,113398835151820+c.lower,113399223263568+c.upper)) = pointBounds57537 := by
 decide +kernel
def cuts57538 : List PrefixCut := [⟨64,214791193,214791316⟩]
theorem checked57538 : checkPrefixCuts (2^48) 7545552897 10 Manual.Count131072.C057538.packed 64 cuts57538 = true := by
 decide +kernel
def cuts57539 : List PrefixCut := [⟨48,160885785,160885877⟩,
⟨64,216652574,216652698⟩]
theorem checked57539 : checkPrefixCuts (2^48) 7545683969 10 Manual.Count131072.C057539.packed 64 cuts57539 = true := by
 decide +kernel
def pointBounds57539 : List (Nat × Nat × Nat) := [(7545782272,113399429242171,113399817354257)]
theorem point_links_checked57539 : (cuts57539.take 1).map (fun c => (7545683969-1+2*2^10*c.k,113399268356386+c.lower,113399656468380+c.upper)) = pointBounds57539 := by
 decide +kernel
def cuts57540 : List PrefixCut := [⟨64,218476614,218476741⟩]
theorem checked57540 : checkPrefixCuts (2^48) 7545815041 10 Manual.Count131072.C057540.packed 64 cuts57540 = true := by
 decide +kernel
def cuts57541 : List PrefixCut := [⟨36,120483163,120483231⟩,
⟨64,213138764,213138883⟩]
theorem checked57541 : checkPrefixCuts (2^48) 7545946113 10 Manual.Count131072.C057541.packed 64 cuts57541 = true := by
 decide +kernel
def pointBounds57541 : List (Nat × Nat × Nat) := [(7546019840,113399823968737,113400212081050)]
theorem point_links_checked57541 : (cuts57541.take 1).map (fun c => (7545946113-1+2*2^10*c.k,113399703485574+c.lower,113400091597819+c.upper)) = pointBounds57541 := by
 decide +kernel
def cuts57542 : List PrefixCut := [⟨64,216007196,216007319⟩]
theorem checked57542 : checkPrefixCuts (2^48) 7546077185 10 Manual.Count131072.C057542.packed 64 cuts57542 = true := by
 decide +kernel
def cuts57543 : List PrefixCut := [⟨24,80232415,80232461⟩,
⟨64,214474148,214474273⟩]
theorem checked57543 : checkPrefixCuts (2^48) 7546208257 10 Manual.Count131072.C057543.packed 64 cuts57543 = true := by
 decide +kernel
def pointBounds57543 : List (Nat × Nat × Nat) := [(7546257408,113400212863949,113400600976482)]
theorem point_links_checked57543 : (cuts57543.take 1).map (fun c => (7546208257-1+2*2^10*c.k,113400132631534+c.lower,113400520744021+c.upper)) = pointBounds57543 := by
 decide +kernel
def cuts57544 : List PrefixCut := [⟨64,212195160,212195282⟩]
theorem checked57544 : checkPrefixCuts (2^48) 7546339329 10 Manual.Count131072.C057544.packed 64 cuts57544 = true := by
 decide +kernel
def cuts57545 : List PrefixCut := [⟨12,40543817,40543841⟩,
⟨64,216741916,216742041⟩]
theorem checked57545 : checkPrefixCuts (2^48) 7546470401 10 Manual.Count131072.C057545.packed 64 cuts57545 = true := by
 decide +kernel
def pointBounds57545 : List (Nat × Nat × Nat) := [(7546494976,113400599844659,113400987957417)]
theorem point_links_checked57545 : (cuts57545.take 1).map (fun c => (7546470401-1+2*2^10*c.k,113400559300842+c.lower,113400947413576+c.upper)) = pointBounds57545 := by
 decide +kernel
def cuts57546 : List PrefixCut := [⟨64,216477056,216477179⟩]
theorem checked57546 : checkPrefixCuts (2^48) 7546601473 10 Manual.Count131072.C057546.packed 64 cuts57546 = true := by
 decide +kernel
def pointBounds57546 : List (Nat × Nat × Nat) := [(7546732544,113400992519814,113401380632796)]
theorem point_links_checked57546 : (cuts57546.take 1).map (fun c => (7546601473-1+2*2^10*c.k,113400776042758+c.lower,113401164155617+c.upper)) = pointBounds57546 := by
 decide +kernel
def cuts57547 : List PrefixCut := [⟨64,215093301,215093424⟩]
theorem checked57547 : checkPrefixCuts (2^48) 7546732545 10 Manual.Count131072.C057547.packed 64 cuts57547 = true := by
 decide +kernel
def cuts57548 : List PrefixCut := [⟨52,175219786,175219881⟩,
⟨64,214530138,214530256⟩]
theorem checked57548 : checkPrefixCuts (2^48) 7546863617 10 Manual.Count131072.C057548.packed 64 cuts57548 = true := by
 decide +kernel
def pointBounds57548 : List (Nat × Nat × Nat) := [(7546970112,113401382832901,113401770946101)]
theorem point_links_checked57548 : (cuts57548.take 1).map (fun c => (7546863617-1+2*2^10*c.k,113401207613115+c.lower,113401595726220+c.upper)) = pointBounds57548 := by
 decide +kernel
def cuts57549 : List PrefixCut := [⟨64,212885369,212885488⟩]
theorem checked57549 : checkPrefixCuts (2^48) 7546994689 10 Manual.Count131072.C057549.packed 64 cuts57549 = true := by
 decide +kernel
def cuts57550 : List PrefixCut := [⟨40,132920948,132921024⟩,
⟨64,214075120,214075242⟩]
theorem checked57550 : checkPrefixCuts (2^48) 7547125761 10 Manual.Count131072.C057550.packed 64 cuts57550 = true := by
 decide +kernel
def pointBounds57550 : List (Nat × Nat × Nat) := [(7547207680,113401767949570,113402156062988)]
theorem point_links_checked57550 : (cuts57550.take 1).map (fun c => (7547125761-1+2*2^10*c.k,113401635028622+c.lower,113402023141964+c.upper)) = pointBounds57550 := by
 decide +kernel
def cuts57551 : List PrefixCut := [⟨64,214220569,214220690⟩]
theorem checked57551 : checkPrefixCuts (2^48) 7547256833 10 Manual.Count131072.C057551.packed 64 cuts57551 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S6.B000235
