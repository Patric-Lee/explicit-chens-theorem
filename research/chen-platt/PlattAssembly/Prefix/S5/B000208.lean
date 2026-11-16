import PlattAssemblyKernel
import PlattCertificates.Count131072.C046656
import PlattCertificates.Count131072.C046657
import PlattCertificates.Count131072.C046658
import PlattCertificates.Count131072.C046659
import PlattCertificates.Count131072.C046660
import PlattCertificates.Count131072.C046661
import PlattCertificates.Count131072.C046662
import PlattCertificates.Count131072.C046663
import PlattCertificates.Count131072.C046664
import PlattCertificates.Count131072.C046665
import PlattCertificates.Count131072.C046666
import PlattCertificates.Count131072.C046667
import PlattCertificates.Count131072.C046668
import PlattCertificates.Count131072.C046669
import PlattCertificates.Count131072.C046670
import PlattCertificates.Count131072.C046671
import PlattCertificates.Count131072.C046672
import PlattCertificates.Count131072.C046673
import PlattCertificates.Count131072.C046674
import PlattCertificates.Count131072.C046675
import PlattCertificates.Count131072.C046676
import PlattCertificates.Count131072.C046677
import PlattCertificates.Count131072.C046678
import PlattCertificates.Count131072.C046679
import PlattCertificates.Count131072.C046680
import PlattCertificates.Count131072.C046681
import PlattCertificates.Count131072.C046682
import PlattCertificates.Count131072.C046683
import PlattCertificates.Count131072.C046684
import PlattCertificates.Count131072.C046685
import PlattCertificates.Count131072.C046686
import PlattCertificates.Count131072.C046687
namespace ChenEffective.PlattWindow.Assembly.Prefix.S5.B000208
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts46656 : List PrefixCut := [⟨64,266512101,266512248⟩]
theorem checked46656 : checkPrefixCuts (2^48) 6119227393 10 Manual.Count131072.C046656.packed 64 cuts46656 = true := by
 decide +kernel
def cuts46657 : List PrefixCut := [⟨12,51195059,51195090⟩,
⟨64,270140142,270140295⟩]
theorem checked46657 : checkPrefixCuts (2^48) 6119358465 10 Manual.Count131072.C046657.packed 64 cuts46657 = true := by
 decide +kernel
def pointBounds46657 : List (Nat × Nat × Nat) := [(6119383040,110794388265328,110794774894416)]
theorem point_links_checked46657 : (cuts46657.take 1).map (fun c => (6119358465-1+2*2^10*c.k,110794337070269+c.lower,110794723699326+c.upper)) = pointBounds46657 := by
 decide +kernel
def cuts46658 : List PrefixCut := [⟨42,175751271,175751369⟩,
⟨64,267374611,267374762⟩]
theorem checked46658 : checkPrefixCuts (2^48) 6119489537 10 Manual.Count131072.C046658.packed 64 cuts46658 = true := by
 decide +kernel
def pointBounds46658 : List (Nat × Nat × Nat) := [(6119575552,110794782961682,110795169590990)]
theorem point_links_checked46658 : (cuts46658.take 1).map (fun c => (6119489537-1+2*2^10*c.k,110794607210411+c.lower,110794993839621+c.upper)) = pointBounds46658 := by
 decide +kernel
def cuts46659 : List PrefixCut := [⟨64,266264987,266265138⟩]
theorem checked46659 : checkPrefixCuts (2^48) 6119620609 10 Manual.Count131072.C046659.packed 64 cuts46659 = true := by
 decide +kernel
def cuts46660 : List PrefixCut := [⟨8,33345966,33345983⟩,
⟨64,268926939,268927092⟩]
theorem checked46660 : checkPrefixCuts (2^48) 6119751681 10 Manual.Count131072.C046660.packed 64 cuts46660 = true := by
 decide +kernel
def pointBounds46660 : List (Nat × Nat × Nat) := [(6119768064,110795174195975,110795560825504)]
theorem point_links_checked46660 : (cuts46660.take 1).map (fun c => (6119751681-1+2*2^10*c.k,110795140850009+c.lower,110795527479521+c.upper)) = pointBounds46660 := by
 decide +kernel
def cuts46661 : List PrefixCut := [⟨38,156376934,156377024⟩,
⟨64,262988066,262988216⟩]
theorem checked46661 : checkPrefixCuts (2^48) 6119882753 10 Manual.Count131072.C046661.packed 64 cuts46661 = true := by
 decide +kernel
def pointBounds46661 : List (Nat × Nat × Nat) := [(6119960576,110795566153882,110795952783637)]
theorem point_links_checked46661 : (cuts46661.take 1).map (fun c => (6119882753-1+2*2^10*c.k,110795409776948+c.lower,110795796406613+c.upper)) = pointBounds46661 := by
 decide +kernel
def cuts46662 : List PrefixCut := [⟨64,268593467,268593617⟩]
theorem checked46662 : checkPrefixCuts (2^48) 6120013825 10 Manual.Count131072.C046662.packed 64 cuts46662 = true := by
 decide +kernel
def cuts46663 : List PrefixCut := [⟨4,18350612,18350623⟩,
⟨64,267667927,267668079⟩]
theorem checked46663 : checkPrefixCuts (2^48) 6120144897 10 Manual.Count131072.C046663.packed 64 cuts46663 = true := by
 decide +kernel
def pointBounds46663 : List (Nat × Nat × Nat) := [(6120153088,110795959709093,110796346339069)]
theorem point_links_checked46663 : (cuts46663.take 1).map (fun c => (6120144897-1+2*2^10*c.k,110795941358481+c.lower,110796327988446+c.upper)) = pointBounds46663 := by
 decide +kernel
def cuts46664 : List PrefixCut := [⟨34,142385952,142386035⟩,
⟨64,268857907,268858066⟩]
theorem checked46664 : checkPrefixCuts (2^48) 6120275969 10 Manual.Count131072.C046664.packed 64 cuts46664 = true := by
 decide +kernel
def pointBounds46664 : List (Nat × Nat × Nat) := [(6120345600,110796351412360,110796738042560)]
theorem point_links_checked46664 : (cuts46664.take 1).map (fun c => (6120275969-1+2*2^10*c.k,110796209026408+c.lower,110796595656525+c.upper)) = pointBounds46664 := by
 decide +kernel
def cuts46665 : List PrefixCut := [⟨64,268530267,268530419⟩]
theorem checked46665 : checkPrefixCuts (2^48) 6120407041 10 Manual.Count131072.C046665.packed 64 cuts46665 = true := by
 decide +kernel
def pointBounds46665 : List (Nat × Nat × Nat) := [(6120538112,110796746414582,110797133045010)]
theorem point_links_checked46665 : (cuts46665.take 1).map (fun c => (6120407041-1+2*2^10*c.k,110796477884315+c.lower,110796864514591+c.upper)) = pointBounds46665 := by
 decide +kernel
def cuts46666 : List PrefixCut := [⟨64,271007840,271007996⟩]
theorem checked46666 : checkPrefixCuts (2^48) 6120538113 10 Manual.Count131072.C046666.packed 64 cuts46666 = true := by
 decide +kernel
def cuts46667 : List PrefixCut := [⟨30,124211882,124211953⟩,
⟨64,264333892,264334044⟩]
theorem checked46667 : checkPrefixCuts (2^48) 6120669185 10 Manual.Count131072.C046667.packed 64 cuts46667 = true := by
 decide +kernel
def pointBounds46667 : List (Nat × Nat × Nat) := [(6120730624,110797141634304,110797528264959)]
theorem point_links_checked46667 : (cuts46667.take 1).map (fun c => (6120669185-1+2*2^10*c.k,110797017422422+c.lower,110797404053006+c.upper)) = pointBounds46667 := by
 decide +kernel
def cuts46668 : List PrefixCut := [⟨60,252280052,252280197⟩,
⟨64,269110805,269110958⟩]
theorem checked46668 : checkPrefixCuts (2^48) 6120800257 10 Manual.Count131072.C046668.packed 64 cuts46668 = true := by
 decide +kernel
def pointBounds46668 : List (Nat × Nat × Nat) := [(6120923136,110797534036366,110797920667247)]
theorem point_links_checked46668 : (cuts46668.take 1).map (fun c => (6120800257-1+2*2^10*c.k,110797281756314+c.lower,110797668387050+c.upper)) = pointBounds46668 := by
 decide +kernel
def cuts46669 : List PrefixCut := [⟨64,272323981,272324135⟩]
theorem checked46669 : checkPrefixCuts (2^48) 6120931329 10 Manual.Count131072.C046669.packed 64 cuts46669 = true := by
 decide +kernel
def cuts46670 : List PrefixCut := [⟨26,107373685,107373746⟩,
⟨64,264914708,264914860⟩]
theorem checked46670 : checkPrefixCuts (2^48) 6121062401 10 Manual.Count131072.C046670.packed 64 cuts46670 = true := by
 decide +kernel
def pointBounds46670 : List (Nat × Nat × Nat) := [(6121115648,110797930564785,110798317195889)]
theorem point_links_checked46670 : (cuts46670.take 1).map (fun c => (6121062401-1+2*2^10*c.k,110797823191100+c.lower,110798209822143+c.upper)) = pointBounds46670 := by
 decide +kernel
def cuts46671 : List PrefixCut := [⟨56,232767126,232767260⟩,
⟨64,266610422,266610576⟩]
theorem checked46671 : checkPrefixCuts (2^48) 6121193473 10 Manual.Count131072.C046671.packed 64 cuts46671 = true := by
 decide +kernel
def pointBounds46671 : List (Nat × Nat × Nat) := [(6121308160,110798320872934,110798707504263)]
theorem point_links_checked46671 : (cuts46671.take 1).map (fun c => (6121193473-1+2*2^10*c.k,110798088105808+c.lower,110798474737003+c.upper)) = pointBounds46671 := by
 decide +kernel
def cuts46672 : List PrefixCut := [⟨64,266742646,266742795⟩]
theorem checked46672 : checkPrefixCuts (2^48) 6121324545 10 Manual.Count131072.C046672.packed 64 cuts46672 = true := by
 decide +kernel
def cuts46673 : List PrefixCut := [⟨22,91825098,91825153⟩,
⟨64,265909294,265909448⟩]
theorem checked46673 : checkPrefixCuts (2^48) 6121455617 10 Manual.Count131072.C046673.packed 64 cuts46673 = true := by
 decide +kernel
def pointBounds46673 : List (Nat × Nat × Nat) := [(6121500672,110798713283974,110799099915527)]
theorem point_links_checked46673 : (cuts46673.take 1).map (fun c => (6121455617-1+2*2^10*c.k,110798621458876+c.lower,110799008090374+c.upper)) = pointBounds46673 := by
 decide +kernel
def cuts46674 : List PrefixCut := [⟨52,214222255,214222380⟩,
⟨64,264937994,264938147⟩]
theorem checked46674 : checkPrefixCuts (2^48) 6121586689 10 Manual.Count131072.C046674.packed 64 cuts46674 = true := by
 decide +kernel
def pointBounds46674 : List (Nat × Nat × Nat) := [(6121693184,110799101590425,110799488222202)]
theorem point_links_checked46674 : (cuts46674.take 1).map (fun c => (6121586689-1+2*2^10*c.k,110798887368170+c.lower,110799273999822+c.upper)) = pointBounds46674 := by
 decide +kernel
def cuts46675 : List PrefixCut := [⟨64,266311723,266311879⟩]
theorem checked46675 : checkPrefixCuts (2^48) 6121717761 10 Manual.Count131072.C046675.packed 64 cuts46675 = true := by
 decide +kernel
def cuts46676 : List PrefixCut := [⟨18,73703698,73703740⟩,
⟨64,268099133,268099291⟩]
theorem checked46676 : checkPrefixCuts (2^48) 6121848833 10 Manual.Count131072.C046676.packed 64 cuts46676 = true := by
 decide +kernel
def pointBounds46676 : List (Nat × Nat × Nat) := [(6121885696,110799492321585,110799878953588)]
theorem point_links_checked46676 : (cuts46676.take 1).map (fun c => (6121848833-1+2*2^10*c.k,110799418617887+c.lower,110799805249848+c.upper)) = pointBounds46676 := by
 decide +kernel
def cuts46677 : List PrefixCut := [⟨48,202024617,202024732⟩,
⟨64,270208346,270208503⟩]
theorem checked46677 : checkPrefixCuts (2^48) 6121979905 10 Manual.Count131072.C046677.packed 64 cuts46677 = true := by
 decide +kernel
def pointBounds46677 : List (Nat × Nat × Nat) := [(6122078208,110799888741637,110800275373871)]
theorem point_links_checked46677 : (cuts46677.take 1).map (fun c => (6121979905-1+2*2^10*c.k,110799686717020+c.lower,110800073349139+c.upper)) = pointBounds46677 := by
 decide +kernel
def cuts46678 : List PrefixCut := [⟨64,261650999,261651151⟩]
theorem checked46678 : checkPrefixCuts (2^48) 6122110977 10 Manual.Count131072.C046678.packed 64 cuts46678 = true := by
 decide +kernel
def cuts46679 : List PrefixCut := [⟨14,58527042,58527072⟩,
⟨64,267989995,267990145⟩]
theorem checked46679 : checkPrefixCuts (2^48) 6122242049 10 Manual.Count131072.C046679.packed 64 cuts46679 = true := by
 decide +kernel
def pointBounds46679 : List (Nat × Nat × Nat) := [(6122270720,110800277103407,110800663735865)]
theorem point_links_checked46679 : (cuts46679.take 1).map (fun c => (6122242049-1+2*2^10*c.k,110800218576365+c.lower,110800605208793+c.upper)) = pointBounds46679 := by
 decide +kernel
def cuts46680 : List PrefixCut := [⟨44,186196579,186196687⟩,
⟨64,268581934,268582093⟩]
theorem checked46680 : checkPrefixCuts (2^48) 6122373121 10 Manual.Count131072.C046680.packed 64 cuts46680 = true := by
 decide +kernel
def pointBounds46680 : List (Nat × Nat × Nat) := [(6122463232,110800672762939,110801059395625)]
theorem point_links_checked46680 : (cuts46680.take 1).map (fun c => (6122373121-1+2*2^10*c.k,110800486566360+c.lower,110800873198938+c.upper)) = pointBounds46680 := by
 decide +kernel
def cuts46681 : List PrefixCut := [⟨64,267472824,267472983⟩]
theorem checked46681 : checkPrefixCuts (2^48) 6122504193 10 Manual.Count131072.C046681.packed 64 cuts46681 = true := by
 decide +kernel
def cuts46682 : List PrefixCut := [⟨10,41973130,41973151⟩,
⟨64,267650998,267651147⟩]
theorem checked46682 : checkPrefixCuts (2^48) 6122635265 10 Manual.Count131072.C046682.packed 64 cuts46682 = true := by
 decide +kernel
def pointBounds46682 : List (Nat × Nat × Nat) := [(6122655744,110801064594248,110801451227165)]
theorem point_links_checked46682 : (cuts46682.take 1).map (fun c => (6122635265-1+2*2^10*c.k,110801022621118+c.lower,110801409254014+c.upper)) = pointBounds46682 := by
 decide +kernel
def cuts46683 : List PrefixCut := [⟨40,166876696,166876791⟩,
⟨64,266036255,266036407⟩]
theorem checked46683 : checkPrefixCuts (2^48) 6122766337 10 Manual.Count131072.C046683.packed 64 cuts46683 = true := by
 decide +kernel
def pointBounds46683 : List (Nat × Nat × Nat) := [(6122848256,110801457148812,110801843781952)]
theorem point_links_checked46683 : (cuts46683.take 1).map (fun c => (6122766337-1+2*2^10*c.k,110801290272116+c.lower,110801676905161+c.upper)) = pointBounds46683 := by
 decide +kernel
def cuts46684 : List PrefixCut := [⟨64,268650858,268651018⟩]
theorem checked46684 : checkPrefixCuts (2^48) 6122897409 10 Manual.Count131072.C046684.packed 64 cuts46684 = true := by
 decide +kernel
def cuts46685 : List PrefixCut := [⟨6,24777742,24777757⟩,
⟨64,267036183,267036340⟩]
theorem checked46685 : checkPrefixCuts (2^48) 6123028481 10 Manual.Count131072.C046685.packed 64 cuts46685 = true := by
 decide +kernel
def pointBounds46685 : List (Nat × Nat × Nat) := [(6123040768,110801849736971,110802236370343)]
theorem point_links_checked46685 : (cuts46685.take 1).map (fun c => (6123028481-1+2*2^10*c.k,110801824959229+c.lower,110802211592586+c.upper)) = pointBounds46685 := by
 decide +kernel
def cuts46686 : List PrefixCut := [⟨36,153719060,153719154⟩,
⟨64,269650677,269650841⟩]
theorem checked46686 : checkPrefixCuts (2^48) 6123159553 10 Manual.Count131072.C046686.packed 64 cuts46686 = true := by
 decide +kernel
def pointBounds46686 : List (Nat × Nat × Nat) := [(6123233280,110802245714472,110802632348080)]
theorem point_links_checked46686 : (cuts46686.take 1).map (fun c => (6123159553-1+2*2^10*c.k,110802091995412+c.lower,110802478628926+c.upper)) = pointBounds46686 := by
 decide +kernel
def cuts46687 : List PrefixCut := [⟨64,266565083,266565237⟩]
theorem checked46687 : checkPrefixCuts (2^48) 6123290625 10 Manual.Count131072.C046687.packed 64 cuts46687 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S5.B000208
