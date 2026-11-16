import PlattAssemblyKernel
import PlattCertificates.Count131072.C054640
import PlattCertificates.Count131072.C054641
import PlattCertificates.Count131072.C054642
import PlattCertificates.Count131072.C054643
import PlattCertificates.Count131072.C054644
import PlattCertificates.Count131072.C054645
import PlattCertificates.Count131072.C054646
import PlattCertificates.Count131072.C054647
import PlattCertificates.Count131072.C054648
import PlattCertificates.Count131072.C054649
import PlattCertificates.Count131072.C054650
import PlattCertificates.Count131072.C054651
import PlattCertificates.Count131072.C054652
import PlattCertificates.Count131072.C054653
import PlattCertificates.Count131072.C054654
import PlattCertificates.Count131072.C054655
import PlattCertificates.Count131072.C054656
import PlattCertificates.Count131072.C054657
import PlattCertificates.Count131072.C054658
import PlattCertificates.Count131072.C054659
import PlattCertificates.Count131072.C054660
import PlattCertificates.Count131072.C054661
import PlattCertificates.Count131072.C054662
import PlattCertificates.Count131072.C054663
import PlattCertificates.Count131072.C054664
import PlattCertificates.Count131072.C054665
import PlattCertificates.Count131072.C054666
import PlattCertificates.Count131072.C054667
import PlattCertificates.Count131072.C054668
import PlattCertificates.Count131072.C054669
import PlattCertificates.Count131072.C054670
import PlattCertificates.Count131072.C054671
namespace ChenEffective.PlattWindow.Assembly.Prefix.S6.B000145
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts54640 : List PrefixCut := [⟨64,227944584,227944713⟩]
theorem checked54640 : checkPrefixCuts (2^48) 7165706241 10 Manual.Count131072.C054640.packed 64 cuts54640 = true := by
 decide +kernel
def cuts54641 : List PrefixCut := [⟨9,31934692,31934710⟩,
⟨64,230768535,230768665⟩]
theorem checked54641 : checkPrefixCuts (2^48) 7165837313 10 Manual.Count131072.C054641.packed 64 cuts54641 = true := by
 decide +kernel
def pointBounds54641 : List (Nat × Nat × Nat) := [(7165855744,112759389825221,112759777573777)]
theorem point_links_checked54641 : (cuts54641.take 1).map (fun c => (7165837313-1+2*2^10*c.k,112759357890529+c.lower,112759745639067+c.upper)) = pointBounds54641 := by
 decide +kernel
def cuts54642 : List PrefixCut := [⟨55,194981393,194981504⟩,
⟨64,228093360,228093490⟩]
theorem checked54642 : checkPrefixCuts (2^48) 7165968385 10 Manual.Count131072.C054642.packed 64 cuts54642 = true := by
 decide +kernel
def pointBounds54642 : List (Nat × Nat × Nat) := [(7166081024,112759783640457,112760171389236)]
theorem point_links_checked54642 : (cuts54642.take 1).map (fun c => (7165968385-1+2*2^10*c.k,112759588659064+c.lower,112759976407732+c.upper)) = pointBounds54642 := by
 decide +kernel
def cuts54643 : List PrefixCut := [⟨64,225536093,225536219⟩]
theorem checked54643 : checkPrefixCuts (2^48) 7166099457 10 Manual.Count131072.C054643.packed 64 cuts54643 = true := by
 decide +kernel
def cuts54644 : List PrefixCut := [⟨37,133151574,133151649⟩,
⟨64,228085029,228085157⟩]
theorem checked54644 : checkPrefixCuts (2^48) 7166230529 10 Manual.Count131072.C054644.packed 64 cuts54644 = true := by
 decide +kernel
def pointBounds54644 : List (Nat × Nat × Nat) := [(7166306304,112760175440091,112760563189090)]
theorem point_links_checked54644 : (cuts54644.take 1).map (fun c => (7166230529-1+2*2^10*c.k,112760042288517+c.lower,112760430037441+c.upper)) = pointBounds54644 := by
 decide +kernel
def cuts54645 : List PrefixCut := [⟨64,227570248,227570378⟩]
theorem checked54645 : checkPrefixCuts (2^48) 7166361601 10 Manual.Count131072.C054645.packed 64 cuts54645 = true := by
 decide +kernel
def cuts54646 : List PrefixCut := [⟨19,67162668,67162706⟩,
⟨64,227094770,227094899⟩]
theorem checked54646 : checkPrefixCuts (2^48) 7166492673 10 Manual.Count131072.C054646.packed 64 cuts54646 = true := by
 decide +kernel
def pointBounds54646 : List (Nat × Nat × Nat) := [(7166531584,112760565106462,112760952855682)]
theorem point_links_checked54646 : (cuts54646.take 1).map (fun c => (7166492673-1+2*2^10*c.k,112760497943794+c.lower,112760885692976+c.upper)) = pointBounds54646 := by
 decide +kernel
def cuts54647 : List PrefixCut := [⟨64,225755230,225755359⟩]
theorem checked54647 : checkPrefixCuts (2^48) 7166623745 10 Manual.Count131072.C054647.packed 64 cuts54647 = true := by
 decide +kernel
def cuts54648 : List PrefixCut := [⟨1,3181281,3181283⟩,
⟨64,229128750,229128879⟩]
theorem checked54648 : checkPrefixCuts (2^48) 7166754817 10 Manual.Count131072.C054648.packed 64 cuts54648 = true := by
 decide +kernel
def pointBounds54648 : List (Nat × Nat × Nat) := [(7166756864,112760953975075,112761341724517)]
theorem point_links_checked54648 : (cuts54648.take 1).map (fun c => (7166754817-1+2*2^10*c.k,112760950793794+c.lower,112761338543234+c.upper)) = pointBounds54648 := by
 decide +kernel
def cuts54649 : List PrefixCut := [⟨47,166404364,166404461⟩,
⟨64,225943356,225943487⟩]
theorem checked54649 : checkPrefixCuts (2^48) 7166885889 10 Manual.Count131072.C054649.packed 64 cuts54649 = true := by
 decide +kernel
def pointBounds54649 : List (Nat × Nat × Nat) := [(7166982144,112761346326908,112761734076574)]
theorem point_links_checked54649 : (cuts54649.take 1).map (fun c => (7166885889-1+2*2^10*c.k,112761179922544+c.lower,112761567672113+c.upper)) = pointBounds54649 := by
 decide +kernel
def cuts54650 : List PrefixCut := [⟨64,227785054,227785183⟩]
theorem checked54650 : checkPrefixCuts (2^48) 7167016961 10 Manual.Count131072.C054650.packed 64 cuts54650 = true := by
 decide +kernel
def cuts54651 : List PrefixCut := [⟨29,101559379,101559436⟩,
⟨64,227152543,227152668⟩]
theorem checked54651 : checkPrefixCuts (2^48) 7167148033 10 Manual.Count131072.C054651.packed 64 cuts54651 = true := by
 decide +kernel
def pointBounds54651 : List (Nat × Nat × Nat) := [(7167207424,112761735210333,112762122960219)]
theorem point_links_checked54651 : (cuts54651.take 1).map (fun c => (7167148033-1+2*2^10*c.k,112761633650954+c.lower,112762021400783+c.upper)) = pointBounds54651 := by
 decide +kernel
def cuts54652 : List PrefixCut := [⟨64,226402221,226402348⟩]
theorem checked54652 : checkPrefixCuts (2^48) 7167279105 10 Manual.Count131072.C054652.packed 64 cuts54652 = true := by
 decide +kernel
def cuts54653 : List PrefixCut := [⟨11,38014743,38014765⟩,
⟨64,227065662,227065792⟩]
theorem checked54653 : checkPrefixCuts (2^48) 7167410177 10 Manual.Count131072.C054653.packed 64 cuts54653 = true := by
 decide +kernel
def pointBounds54653 : List (Nat × Nat × Nat) := [(7167432704,112762125220461,112762512970564)]
theorem point_links_checked54653 : (cuts54653.take 1).map (fun c => (7167410177-1+2*2^10*c.k,112762087205718+c.lower,112762474955799+c.upper)) = pointBounds54653 := by
 decide +kernel
def cuts54654 : List PrefixCut := [⟨57,199925879,199925995⟩,
⟨64,224980200,224980330⟩]
theorem checked54654 : checkPrefixCuts (2^48) 7167541249 10 Manual.Count131072.C054654.packed 64 cuts54654 = true := by
 decide +kernel
def pointBounds54654 : List (Nat × Nat × Nat) := [(7167657984,112762514197259,112762901947586)]
theorem point_links_checked54654 : (cuts54654.take 1).map (fun c => (7167541249-1+2*2^10*c.k,112762314271380+c.lower,112762702021591+c.upper)) = pointBounds54654 := by
 decide +kernel
def cuts54655 : List PrefixCut := [⟨64,224936829,224936961⟩]
theorem checked54655 : checkPrefixCuts (2^48) 7167672321 10 Manual.Count131072.C054655.packed 64 cuts54655 = true := by
 decide +kernel
def cuts54656 : List PrefixCut := [⟨39,138777076,138777155⟩,
⟨64,227995700,227995829⟩]
theorem checked54656 : checkPrefixCuts (2^48) 7167803393 10 Manual.Count131072.C054656.packed 64 cuts54656 = true := by
 decide +kernel
def pointBounds54656 : List (Nat × Nat × Nat) := [(7167883264,112762902965485,112763290716037)]
theorem point_links_checked54656 : (cuts54656.take 1).map (fun c => (7167803393-1+2*2^10*c.k,112762764188409+c.lower,112763151938882+c.upper)) = pointBounds54656 := by
 decide +kernel
def cuts54657 : List PrefixCut := [⟨64,227912978,227913101⟩]
theorem checked54657 : checkPrefixCuts (2^48) 7167934465 10 Manual.Count131072.C054657.packed 64 cuts54657 = true := by
 decide +kernel
def cuts54658 : List PrefixCut := [⟨21,74294653,74294695⟩,
⟨64,226887859,226887989⟩]
theorem checked54658 : checkPrefixCuts (2^48) 7168065537 10 Manual.Count131072.C054658.packed 64 cuts54658 = true := by
 decide +kernel
def pointBounds54658 : List (Nat × Nat × Nat) := [(7168108544,112763294391740,112763682142507)]
theorem point_links_checked54658 : (cuts54658.take 1).map (fun c => (7168065537-1+2*2^10*c.k,112763220097087+c.lower,112763607847812+c.upper)) = pointBounds54658 := by
 decide +kernel
def cuts54659 : List PrefixCut := [⟨64,224841841,224841969⟩]
theorem checked54659 : checkPrefixCuts (2^48) 7168196609 10 Manual.Count131072.C054659.packed 64 cuts54659 = true := by
 decide +kernel
def cuts54660 : List PrefixCut := [⟨3,10327076,10327082⟩,
⟨64,231473702,231473829⟩]
theorem checked54660 : checkPrefixCuts (2^48) 7168327681 10 Manual.Count131072.C054660.packed 64 cuts54660 = true := by
 decide +kernel
def pointBounds54660 : List (Nat × Nat × Nat) := [(7168333824,112763682153863,112764069904852)]
theorem point_links_checked54660 : (cuts54660.take 1).map (fun c => (7168327681-1+2*2^10*c.k,112763671826787+c.lower,112764059577770+c.upper)) = pointBounds54660 := by
 decide +kernel
def cuts54661 : List PrefixCut := [⟨49,170215834,170215932⟩,
⟨64,223380797,223380927⟩]
theorem checked54661 : checkPrefixCuts (2^48) 7168458753 10 Manual.Count131072.C054661.packed 64 cuts54661 = true := by
 decide +kernel
def pointBounds54661 : List (Nat × Nat × Nat) := [(7168559104,112764073516323,112764461267531)]
theorem point_links_checked54661 : (cuts54661.take 1).map (fun c => (7168458753-1+2*2^10*c.k,112763903300489+c.lower,112764291051599+c.upper)) = pointBounds54661 := by
 decide +kernel
def cuts54662 : List PrefixCut := [⟨64,225850377,225850505⟩]
theorem checked54662 : checkPrefixCuts (2^48) 7168589825 10 Manual.Count131072.C054662.packed 64 cuts54662 = true := by
 decide +kernel
def cuts54663 : List PrefixCut := [⟨31,109232832,109232895⟩,
⟨64,224472024,224472153⟩]
theorem checked54663 : checkPrefixCuts (2^48) 7168720897 10 Manual.Count131072.C054663.packed 64 cuts54663 = true := by
 decide +kernel
def pointBounds54663 : List (Nat × Nat × Nat) := [(7168784384,112764461764495,112764849515926)]
theorem point_links_checked54663 : (cuts54663.take 1).map (fun c => (7168720897-1+2*2^10*c.k,112764352531663+c.lower,112764740283031+c.upper)) = pointBounds54663 := by
 decide +kernel
def cuts54664 : List PrefixCut := [⟨64,228708365,228708493⟩]
theorem checked54664 : checkPrefixCuts (2^48) 7168851969 10 Manual.Count131072.C054664.packed 64 cuts54664 = true := by
 decide +kernel
def cuts54665 : List PrefixCut := [⟨13,47193892,47193918⟩,
⟨64,227761872,227762001⟩]
theorem checked54665 : checkPrefixCuts (2^48) 7168983041 10 Manual.Count131072.C054665.packed 64 cuts54665 = true := by
 decide +kernel
def pointBounds54665 : List (Nat × Nat × Nat) := [(7169009664,112764852905944,112765240657595)]
theorem point_links_checked54665 : (cuts54665.take 1).map (fun c => (7168983041-1+2*2^10*c.k,112764805712052+c.lower,112765193463677+c.upper)) = pointBounds54665 := by
 decide +kernel
def cuts54666 : List PrefixCut := [⟨59,210639711,210639833⟩,
⟨64,228268111,228268243⟩]
theorem checked54666 : checkPrefixCuts (2^48) 7169114113 10 Manual.Count131072.C054666.packed 64 cuts54666 = true := by
 decide +kernel
def pointBounds54666 : List (Nat × Nat × Nat) := [(7169234944,112765244113635,112765631865511)]
theorem point_links_checked54666 : (cuts54666.take 1).map (fun c => (7169114113-1+2*2^10*c.k,112765033473924+c.lower,112765421225678+c.upper)) = pointBounds54666 := by
 decide +kernel
def cuts54667 : List PrefixCut := [⟨64,226536452,226536580⟩]
theorem checked54667 : checkPrefixCuts (2^48) 7169245185 10 Manual.Count131072.C054667.packed 64 cuts54667 = true := by
 decide +kernel
def cuts54668 : List PrefixCut := [⟨41,144635646,144635729⟩,
⟨64,224765583,224765712⟩]
theorem checked54668 : checkPrefixCuts (2^48) 7169376257 10 Manual.Count131072.C054668.packed 64 cuts54668 = true := by
 decide +kernel
def pointBounds54668 : List (Nat × Nat × Nat) := [(7169460224,112765632914133,112766020666230)]
theorem point_links_checked54668 : (cuts54668.take 1).map (fun c => (7169376257-1+2*2^10*c.k,112765488278487+c.lower,112765876030501+c.upper)) = pointBounds54668 := by
 decide +kernel
def cuts54669 : List PrefixCut := [⟨64,224643716,224643842⟩]
theorem checked54669 : checkPrefixCuts (2^48) 7169507329 10 Manual.Count131072.C054669.packed 64 cuts54669 = true := by
 decide +kernel
def cuts54670 : List PrefixCut := [⟨23,82993864,82993912⟩,
⟨64,228997335,228997467⟩]
theorem checked54670 : checkPrefixCuts (2^48) 7169638401 10 Manual.Count131072.C054670.packed 64 cuts54670 = true := by
 decide +kernel
def pointBounds54670 : List (Nat × Nat × Nat) := [(7169685504,112766020681650,112766408433967)]
theorem point_links_checked54670 : (cuts54670.take 1).map (fun c => (7169638401-1+2*2^10*c.k,112765937687786+c.lower,112766325440055+c.upper)) = pointBounds54670 := by
 decide +kernel
def cuts54671 : List PrefixCut := [⟨64,227148028,227148160⟩]
theorem checked54671 : checkPrefixCuts (2^48) 7169769473 10 Manual.Count131072.C054671.packed 64 cuts54671 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S6.B000145
