import PlattAssemblyKernel
import PlattCertificates.Count131072.C057712
import PlattCertificates.Count131072.C057713
import PlattCertificates.Count131072.C057714
import PlattCertificates.Count131072.C057715
import PlattCertificates.Count131072.C057716
import PlattCertificates.Count131072.C057717
import PlattCertificates.Count131072.C057718
import PlattCertificates.Count131072.C057719
import PlattCertificates.Count131072.C057720
import PlattCertificates.Count131072.C057721
import PlattCertificates.Count131072.C057722
import PlattCertificates.Count131072.C057723
import PlattCertificates.Count131072.C057724
import PlattCertificates.Count131072.C057725
import PlattCertificates.Count131072.C057726
import PlattCertificates.Count131072.C057727
import PlattCertificates.Count131072.C057728
import PlattCertificates.Count131072.C057729
import PlattCertificates.Count131072.C057730
import PlattCertificates.Count131072.C057731
import PlattCertificates.Count131072.C057732
import PlattCertificates.Count131072.C057733
import PlattCertificates.Count131072.C057734
import PlattCertificates.Count131072.C057735
import PlattCertificates.Count131072.C057736
import PlattCertificates.Count131072.C057737
import PlattCertificates.Count131072.C057738
import PlattCertificates.Count131072.C057739
import PlattCertificates.Count131072.C057740
import PlattCertificates.Count131072.C057741
import PlattCertificates.Count131072.C057742
import PlattCertificates.Count131072.C057743
namespace ChenEffective.PlattWindow.Assembly.Prefix.S6.B000241
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts57712 : List PrefixCut := [⟨64,211280282,211280404⟩]
theorem checked57712 : checkPrefixCuts (2^48) 7568359425 10 Manual.Count131072.C057712.packed 64 cuts57712 = true := by
 decide +kernel
def cuts57713 : List PrefixCut := [⟨48,164194369,164194462⟩,
⟨64,218454283,218454408⟩]
theorem checked57713 : checkPrefixCuts (2^48) 7568490497 10 Manual.Count131072.C057713.packed 64 cuts57713 = true := by
 decide +kernel
def pointBounds57713 : List (Nat × Nat × Nat) := [(7568588800,113436783151254,113437171284603)]
theorem point_links_checked57713 : (cuts57713.take 1).map (fun c => (7568490497-1+2*2^10*c.k,113436618956885+c.lower,113437007090141+c.upper)) = pointBounds57713 := by
 decide +kernel
def cuts57714 : List PrefixCut := [⟨64,212277080,212277203⟩]
theorem checked57714 : checkPrefixCuts (2^48) 7568621569 10 Manual.Count131072.C057714.packed 64 cuts57714 = true := by
 decide +kernel
def cuts57715 : List PrefixCut := [⟨36,120231680,120231751⟩,
⟨64,214913776,214913899⟩]
theorem checked57715 : checkPrefixCuts (2^48) 7568752641 10 Manual.Count131072.C057715.packed 64 cuts57715 = true := by
 decide +kernel
def pointBounds57715 : List (Nat × Nat × Nat) := [(7568826368,113437169919928,113437558053503)]
theorem point_links_checked57715 : (cuts57715.take 1).map (fun c => (7568752641-1+2*2^10*c.k,113437049688248+c.lower,113437437821752+c.upper)) = pointBounds57715 := by
 decide +kernel
def cuts57716 : List PrefixCut := [⟨64,217736386,217736509⟩]
theorem checked57716 : checkPrefixCuts (2^48) 7568883713 10 Manual.Count131072.C057716.packed 64 cuts57716 = true := by
 decide +kernel
def cuts57717 : List PrefixCut := [⟨24,79395665,79395709⟩,
⟨64,214943525,214943646⟩]
theorem checked57717 : checkPrefixCuts (2^48) 7569014785 10 Manual.Count131072.C057717.packed 64 cuts57717 = true := by
 decide +kernel
def pointBounds57717 : List (Nat × Nat × Nat) := [(7569063936,113437561734075,113437949867869)]
theorem point_links_checked57717 : (cuts57717.take 1).map (fun c => (7569014785-1+2*2^10*c.k,113437482338410+c.lower,113437870472160+c.upper)) = pointBounds57717 := by
 decide +kernel
def cuts57718 : List PrefixCut := [⟨64,214791070,214791191⟩]
theorem checked57718 : checkPrefixCuts (2^48) 7569145857 10 Manual.Count131072.C057718.packed 64 cuts57718 = true := by
 decide +kernel
def cuts57719 : List PrefixCut := [⟨12,40867893,40867917⟩,
⟨64,211812470,211812590⟩]
theorem checked57719 : checkPrefixCuts (2^48) 7569276929 10 Manual.Count131072.C057719.packed 64 cuts57719 = true := by
 decide +kernel
def pointBounds57719 : List (Nat × Nat × Nat) := [(7569301504,113437952940898,113438341074914)]
theorem point_links_checked57719 : (cuts57719.take 1).map (fun c => (7569276929-1+2*2^10*c.k,113437912073005+c.lower,113438300206997+c.upper)) = pointBounds57719 := by
 decide +kernel
def cuts57720 : List PrefixCut := [⟨64,213556485,213556610⟩]
theorem checked57720 : checkPrefixCuts (2^48) 7569408001 10 Manual.Count131072.C057720.packed 64 cuts57720 = true := by
 decide +kernel
def pointBounds57720 : List (Nat × Nat × Nat) := [(7569539072,113438337441960,113438725576197)]
theorem point_links_checked57720 : (cuts57720.take 1).map (fun c => (7569408001-1+2*2^10*c.k,113438123885475+c.lower,113438512019587+c.upper)) = pointBounds57720 := by
 decide +kernel
def cuts57721 : List PrefixCut := [⟨64,213775912,213776037⟩]
theorem checked57721 : checkPrefixCuts (2^48) 7569539073 10 Manual.Count131072.C057721.packed 64 cuts57721 = true := by
 decide +kernel
def cuts57722 : List PrefixCut := [⟨52,175547101,175547202⟩,
⟨64,215222410,215222533⟩]
theorem checked57722 : checkPrefixCuts (2^48) 7569670145 10 Manual.Count131072.C057722.packed 64 cuts57722 = true := by
 decide +kernel
def pointBounds57722 : List (Nat × Nat × Nat) := [(7569776640,113438726764973,113439114899436)]
theorem point_links_checked57722 : (cuts57722.take 1).map (fun c => (7569670145-1+2*2^10*c.k,113438551217872+c.lower,113438939352234+c.upper)) = pointBounds57722 := by
 decide +kernel
def cuts57723 : List PrefixCut := [⟨64,211983684,211983808⟩]
theorem checked57723 : checkPrefixCuts (2^48) 7569801217 10 Manual.Count131072.C057723.packed 64 cuts57723 = true := by
 decide +kernel
def cuts57724 : List PrefixCut := [⟨40,133487246,133487323⟩,
⟨64,212165957,212166080⟩]
theorem checked57724 : checkPrefixCuts (2^48) 7569932289 10 Manual.Count131072.C057724.packed 64 cuts57724 = true := by
 decide +kernel
def pointBounds57724 : List (Nat × Nat × Nat) := [(7570014208,113439111911212,113439500045898)]
theorem point_links_checked57724 : (cuts57724.take 1).map (fun c => (7569932289-1+2*2^10*c.k,113438978423966+c.lower,113439366558575+c.upper)) = pointBounds57724 := by
 decide +kernel
def cuts57725 : List PrefixCut := [⟨64,213984223,213984344⟩]
theorem checked57725 : checkPrefixCuts (2^48) 7570063361 10 Manual.Count131072.C057725.packed 64 cuts57725 = true := by
 decide +kernel
def cuts57726 : List PrefixCut := [⟨28,91839172,91839224⟩,
⟨64,213088133,213088255⟩]
theorem checked57726 : checkPrefixCuts (2^48) 7570194433 10 Manual.Count131072.C057726.packed 64 cuts57726 = true := by
 decide +kernel
def pointBounds57726 : List (Nat × Nat × Nat) := [(7570251776,113439496413318,113439884548223)]
theorem point_links_checked57726 : (cuts57726.take 1).map (fun c => (7570194433-1+2*2^10*c.k,113439404574146+c.lower,113439792708999+c.upper)) = pointBounds57726 := by
 decide +kernel
def cuts57727 : List PrefixCut := [⟨64,214237054,214237176⟩]
theorem checked57727 : checkPrefixCuts (2^48) 7570325505 10 Manual.Count131072.C057727.packed 64 cuts57727 = true := by
 decide +kernel
def cuts57728 : List PrefixCut := [⟨16,53986264,53986296⟩,
⟨64,212746148,212746269⟩]
theorem checked57728 : checkPrefixCuts (2^48) 7570456577 10 Manual.Count131072.C057728.packed 64 cuts57728 = true := by
 decide +kernel
def pointBounds57728 : List (Nat × Nat × Nat) := [(7570489344,113439885885597,113440274020726)]
theorem point_links_checked57728 : (cuts57728.take 1).map (fun c => (7570456577-1+2*2^10*c.k,113439831899333+c.lower,113440220034430+c.upper)) = pointBounds57728 := by
 decide +kernel
def cuts57729 : List PrefixCut := [⟨64,211998864,211998985⟩]
theorem checked57729 : checkPrefixCuts (2^48) 7570587649 10 Manual.Count131072.C057729.packed 64 cuts57729 = true := by
 decide +kernel
def cuts57730 : List PrefixCut := [⟨4,13087147,13087155⟩,
⟨64,217274633,217274753⟩]
theorem checked57730 : checkPrefixCuts (2^48) 7570718721 10 Manual.Count131072.C057730.packed 64 cuts57730 = true := by
 decide +kernel
def pointBounds57730 : List (Nat × Nat × Nat) := [(7570726912,113440269731492,113440657866839)]
theorem point_links_checked57730 : (cuts57730.take 1).map (fun c => (7570718721-1+2*2^10*c.k,113440256644345+c.lower,113440644779684+c.upper)) = pointBounds57730 := by
 decide +kernel
def cuts57731 : List PrefixCut := [⟨56,191915368,191915478⟩,
⟨64,220096422,220096547⟩]
theorem checked57731 : checkPrefixCuts (2^48) 7570849793 10 Manual.Count131072.C057731.packed 64 cuts57731 = true := by
 decide +kernel
def pointBounds57731 : List (Nat × Nat × Nat) := [(7570964480,113440665834346,113441053969915)]
theorem point_links_checked57731 : (cuts57731.take 1).map (fun c => (7570849793-1+2*2^10*c.k,113440473918978+c.lower,113440862054437+c.upper)) = pointBounds57731 := by
 decide +kernel
def cuts57732 : List PrefixCut := [⟨64,215779986,215780112⟩]
theorem checked57732 : checkPrefixCuts (2^48) 7570980865 10 Manual.Count131072.C057732.packed 64 cuts57732 = true := by
 decide +kernel
def cuts57733 : List PrefixCut := [⟨44,147445040,147445127⟩,
⟨64,215069899,215070024⟩]
theorem checked57733 : checkPrefixCuts (2^48) 7571111937 10 Manual.Count131072.C057733.packed 64 cuts57733 = true := by
 decide +kernel
def pointBounds57733 : List (Nat × Nat × Nat) := [(7571202048,113441057240426,113441445376223)]
theorem point_links_checked57733 : (cuts57733.take 1).map (fun c => (7571111937-1+2*2^10*c.k,113440909795386+c.lower,113441297931096+c.upper)) = pointBounds57733 := by
 decide +kernel
def cuts57734 : List PrefixCut := [⟨64,213690633,213690756⟩]
theorem checked57734 : checkPrefixCuts (2^48) 7571243009 10 Manual.Count131072.C057734.packed 64 cuts57734 = true := by
 decide +kernel
def cuts57735 : List PrefixCut := [⟨32,108070734,108070793⟩,
⟨64,213501061,213501179⟩]
theorem checked57735 : checkPrefixCuts (2^48) 7571374081 10 Manual.Count131072.C057735.packed 64 cuts57735 = true := by
 decide +kernel
def pointBounds57735 : List (Nat × Nat × Nat) := [(7571439616,113441446626652,113441834762669)]
theorem point_links_checked57735 : (cuts57735.take 1).map (fun c => (7571374081-1+2*2^10*c.k,113441338555918+c.lower,113441726691876+c.upper)) = pointBounds57735 := by
 decide +kernel
def cuts57736 : List PrefixCut := [⟨64,215170227,215170352⟩]
theorem checked57736 : checkPrefixCuts (2^48) 7571505153 10 Manual.Count131072.C057736.packed 64 cuts57736 = true := by
 decide +kernel
def cuts57737 : List PrefixCut := [⟨20,68290124,68290163⟩,
⟨64,215612629,215612752⟩]
theorem checked57737 : checkPrefixCuts (2^48) 7571636225 10 Manual.Count131072.C057737.packed 64 cuts57737 = true := by
 decide +kernel
def pointBounds57737 : List (Nat × Nat × Nat) := [(7571677184,113441835517330,113442223653570)]
theorem point_links_checked57737 : (cuts57737.take 1).map (fun c => (7571636225-1+2*2^10*c.k,113441767227206+c.lower,113442155363407+c.upper)) = pointBounds57737 := by
 decide +kernel
def cuts57738 : List PrefixCut := [⟨64,213713013,213713137⟩]
theorem checked57738 : checkPrefixCuts (2^48) 7571767297 10 Manual.Count131072.C057738.packed 64 cuts57738 = true := by
 decide +kernel
def cuts57739 : List PrefixCut := [⟨8,26058682,26058697⟩,
⟨64,213746478,213746599⟩]
theorem checked57739 : checkPrefixCuts (2^48) 7571898369 10 Manual.Count131072.C057739.packed 64 cuts57739 = true := by
 decide +kernel
def pointBounds57739 : List (Nat × Nat × Nat) := [(7571914752,113442222611530,113442610747993)]
theorem point_links_checked57739 : (cuts57739.take 1).map (fun c => (7571898369-1+2*2^10*c.k,113442196552848+c.lower,113442584689296+c.upper)) = pointBounds57739 := by
 decide +kernel
def cuts57740 : List PrefixCut := [⟨60,199282710,199282826⟩,
⟨64,212701930,212702054⟩]
theorem checked57740 : checkPrefixCuts (2^48) 7572029441 10 Manual.Count131072.C057740.packed 64 cuts57740 = true := by
 decide +kernel
def pointBounds57740 : List (Nat × Nat × Nat) := [(7572152320,113442609582036,113442997718721)]
theorem point_links_checked57740 : (cuts57740.take 1).map (fun c => (7572029441-1+2*2^10*c.k,113442410299326+c.lower,113442798435895+c.upper)) = pointBounds57740 := by
 decide +kernel
def cuts57741 : List PrefixCut := [⟨64,213590389,213590514⟩]
theorem checked57741 : checkPrefixCuts (2^48) 7572160513 10 Manual.Count131072.C057741.packed 64 cuts57741 = true := by
 decide +kernel
def cuts57742 : List PrefixCut := [⟨48,161249751,161249843⟩,
⟨64,214999205,214999329⟩]
theorem checked57742 : checkPrefixCuts (2^48) 7572291585 10 Manual.Count131072.C057742.packed 64 cuts57742 = true := by
 decide +kernel
def pointBounds57742 : List (Nat × Nat × Nat) := [(7572389888,113442997841396,113443385978306)]
theorem point_links_checked57742 : (cuts57742.take 1).map (fun c => (7572291585-1+2*2^10*c.k,113442836591645+c.lower,113443224728463+c.upper)) = pointBounds57742 := by
 decide +kernel
def cuts57743 : List PrefixCut := [⟨64,213248467,213248591⟩]
theorem checked57743 : checkPrefixCuts (2^48) 7572422657 10 Manual.Count131072.C057743.packed 64 cuts57743 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S6.B000241
