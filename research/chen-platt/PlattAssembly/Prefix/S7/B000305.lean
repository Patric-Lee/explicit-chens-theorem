import PlattAssemblyKernel
import PlattCertificates.Count131072.C069760
import PlattCertificates.Count131072.C069761
import PlattCertificates.Count131072.C069762
import PlattCertificates.Count131072.C069763
import PlattCertificates.Count131072.C069764
import PlattCertificates.Count131072.C069765
import PlattCertificates.Count131072.C069766
import PlattCertificates.Count131072.C069767
import PlattCertificates.Count131072.C069768
import PlattCertificates.Count131072.C069769
import PlattCertificates.Count131072.C069770
import PlattCertificates.Count131072.C069771
import PlattCertificates.Count131072.C069772
import PlattCertificates.Count131072.C069773
import PlattCertificates.Count131072.C069774
import PlattCertificates.Count131072.C069775
import PlattCertificates.Count131072.C069776
import PlattCertificates.Count131072.C069777
import PlattCertificates.Count131072.C069778
import PlattCertificates.Count131072.C069779
import PlattCertificates.Count131072.C069780
import PlattCertificates.Count131072.C069781
import PlattCertificates.Count131072.C069782
import PlattCertificates.Count131072.C069783
import PlattCertificates.Count131072.C069784
import PlattCertificates.Count131072.C069785
import PlattCertificates.Count131072.C069786
import PlattCertificates.Count131072.C069787
import PlattCertificates.Count131072.C069788
import PlattCertificates.Count131072.C069789
import PlattCertificates.Count131072.C069790
import PlattCertificates.Count131072.C069791
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000305
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts69760 : List PrefixCut := [⟨58,160344759,160344857⟩,
⟨64,176837598,176837704⟩]
theorem checked69760 : checkPrefixCuts (2^48) 9147514881 10 Manual.Count131072.C069760.packed 64 cuts69760 = true := by
 decide +kernel
def pointBounds69760 : List (Nat × Nat × Nat) := [(9147633664,115771784101482,115772173581958)]
theorem point_links_checked69760 : (cuts69760.take 1).map (fun c => (9147514881-1+2*2^10*c.k,115771623756723+c.lower,115772013237101+c.upper)) = pointBounds69760 := by
 decide +kernel
def cuts69761 : List PrefixCut := [⟨64,175973527,175973625⟩]
theorem checked69761 : checkPrefixCuts (2^48) 9147645953 10 Manual.Count131072.C069761.packed 64 cuts69761 = true := by
 decide +kernel
def cuts69762 : List PrefixCut := [⟨64,175724833,175724937⟩]
theorem checked69762 : checkPrefixCuts (2^48) 9147777025 10 Manual.Count131072.C069762.packed 64 cuts69762 = true := by
 decide +kernel
def cuts69763 : List PrefixCut := [⟨6,17692346,17692356⟩,
⟨64,172614651,172614754⟩]
theorem checked69763 : checkPrefixCuts (2^48) 9147908097 10 Manual.Count131072.C069763.packed 64 cuts69763 = true := by
 decide +kernel
def pointBounds69763 : List (Nat × Nat × Nat) := [(9147920384,115772169985027,115772559465723)]
theorem point_links_checked69763 : (cuts69763.take 1).map (fun c => (9147908097-1+2*2^10*c.k,115772152292681+c.lower,115772541773367+c.upper)) = pointBounds69763 := by
 decide +kernel
def cuts69764 : List PrefixCut := [⟨64,172673698,172673798⟩]
theorem checked69764 : checkPrefixCuts (2^48) 9148039169 10 Manual.Count131072.C069764.packed 64 cuts69764 = true := by
 decide +kernel
def cuts69765 : List PrefixCut := [⟨18,49444779,49444809⟩,
⟨64,175809583,175809685⟩]
theorem checked69765 : checkPrefixCuts (2^48) 9148170241 10 Manual.Count131072.C069765.packed 64 cuts69765 = true := by
 decide +kernel
def pointBounds69765 : List (Nat × Nat × Nat) := [(9148207104,115772547025809,115772936506728)]
theorem point_links_checked69765 : (cuts69765.take 1).map (fun c => (9148170241-1+2*2^10*c.k,115772497581030+c.lower,115772887061919+c.upper)) = pointBounds69765 := by
 decide +kernel
def cuts69766 : List PrefixCut := [⟨64,173622558,173622659⟩]
theorem checked69766 : checkPrefixCuts (2^48) 9148301313 10 Manual.Count131072.C069766.packed 64 cuts69766 = true := by
 decide +kernel
def cuts69767 : List PrefixCut := [⟨30,81779877,81779931⟩,
⟨64,176512182,176512291⟩]
theorem checked69767 : checkPrefixCuts (2^48) 9148432385 10 Manual.Count131072.C069767.packed 64 cuts69767 = true := by
 decide +kernel
def pointBounds69767 : List (Nat × Nat × Nat) := [(9148493824,115772928793048,115773318274194)]
theorem point_links_checked69767 : (cuts69767.take 1).map (fun c => (9148432385-1+2*2^10*c.k,115772847013171+c.lower,115773236494263+c.upper)) = pointBounds69767 := by
 decide +kernel
def cuts69768 : List PrefixCut := [⟨64,176909647,176909753⟩]
theorem checked69768 : checkPrefixCuts (2^48) 9148563457 10 Manual.Count131072.C069768.packed 64 cuts69768 = true := by
 decide +kernel
def cuts69769 : List PrefixCut := [⟨42,115559079,115559148⟩,
⟨64,174384261,174384364⟩]
theorem checked69769 : checkPrefixCuts (2^48) 9148694529 10 Manual.Count131072.C069769.packed 64 cuts69769 = true := by
 decide +kernel
def pointBounds69769 : List (Nat × Nat × Nat) := [(9148780544,115773315994079,115773705475455)]
theorem point_links_checked69769 : (cuts69769.take 1).map (fun c => (9148694529-1+2*2^10*c.k,115773200435000+c.lower,115773589916307+c.upper)) = pointBounds69769 := by
 decide +kernel
def cuts69770 : List PrefixCut := [⟨64,175827760,175827866⟩]
theorem checked69770 : checkPrefixCuts (2^48) 9148825601 10 Manual.Count131072.C069770.packed 64 cuts69770 = true := by
 decide +kernel
def cuts69771 : List PrefixCut := [⟨54,148567121,148567207⟩,
⟨64,175856019,175856120⟩]
theorem checked69771 : checkPrefixCuts (2^48) 9148956673 10 Manual.Count131072.C069771.packed 64 cuts69771 = true := by
 decide +kernel
def pointBounds69771 : List (Nat × Nat × Nat) := [(9149067264,115773699214142,115774088695744)]
theorem point_links_checked69771 : (cuts69771.take 1).map (fun c => (9148956673-1+2*2^10*c.k,115773550647021+c.lower,115773940128537+c.upper)) = pointBounds69771 := by
 decide +kernel
def cuts69772 : List PrefixCut := [⟨64,176161143,176161250⟩]
theorem checked69772 : checkPrefixCuts (2^48) 9149087745 10 Manual.Count131072.C069772.packed 64 cuts69772 = true := by
 decide +kernel
def cuts69773 : List PrefixCut := [⟨64,178096791,178096885⟩]
theorem checked69773 : checkPrefixCuts (2^48) 9149218817 10 Manual.Count131072.C069773.packed 64 cuts69773 = true := by
 decide +kernel
def cuts69774 : List PrefixCut := [⟨2,5783719,5783722⟩,
⟨64,177109778,177109881⟩]
theorem checked69774 : checkPrefixCuts (2^48) 9149349889 10 Manual.Count131072.C069774.packed 64 cuts69774 = true := by
 decide +kernel
def pointBounds69774 : List (Nat × Nat × Nat) := [(9149353984,115774086544693,115774476026514)]
theorem point_links_checked69774 : (cuts69774.take 1).map (fun c => (9149349889-1+2*2^10*c.k,115774080760974+c.lower,115774470242792+c.upper)) = pointBounds69774 := by
 decide +kernel
def cuts69775 : List PrefixCut := [⟨64,175815169,175815270⟩]
theorem checked69775 : checkPrefixCuts (2^48) 9149480961 10 Manual.Count131072.C069775.packed 64 cuts69775 = true := by
 decide +kernel
def cuts69776 : List PrefixCut := [⟨14,38392898,38392921⟩,
⟨64,175228139,175228241⟩]
theorem checked69776 : checkPrefixCuts (2^48) 9149612033 10 Manual.Count131072.C069776.packed 64 cuts69776 = true := by
 decide +kernel
def pointBounds69776 : List (Nat × Nat × Nat) := [(9149640704,115774472078819,115774861560864)]
theorem point_links_checked69776 : (cuts69776.take 1).map (fun c => (9149612033-1+2*2^10*c.k,115774433685921+c.lower,115774823167943+c.upper)) = pointBounds69776 := by
 decide +kernel
def cuts69777 : List PrefixCut := [⟨64,174794946,174795050⟩]
theorem checked69777 : checkPrefixCuts (2^48) 9149743105 10 Manual.Count131072.C069777.packed 64 cuts69777 = true := by
 decide +kernel
def cuts69778 : List PrefixCut := [⟨26,71646135,71646174⟩,
⟨64,175315417,175315517⟩]
theorem checked69778 : checkPrefixCuts (2^48) 9149874177 10 Manual.Count131072.C069778.packed 64 cuts69778 = true := by
 decide +kernel
def pointBounds69778 : List (Nat × Nat × Nat) := [(9149927424,115774855355141,115775244837408)]
theorem point_links_checked69778 : (cuts69778.take 1).map (fun c => (9149874177-1+2*2^10*c.k,115774783709006+c.lower,115775173191234+c.upper)) = pointBounds69778 := by
 decide +kernel
def cuts69779 : List PrefixCut := [⟨64,176266515,176266615⟩]
theorem checked69779 : checkPrefixCuts (2^48) 9150005249 10 Manual.Count131072.C069779.packed 64 cuts69779 = true := by
 decide +kernel
def cuts69780 : List PrefixCut := [⟨38,104343669,104343731⟩,
⟨64,173803077,173803177⟩]
theorem checked69780 : checkPrefixCuts (2^48) 9150136321 10 Manual.Count131072.C069780.packed 64 cuts69780 = true := by
 decide +kernel
def pointBounds69780 : List (Nat × Nat × Nat) := [(9150214144,115775239634607,115775629117097)]
theorem point_links_checked69780 : (cuts69780.take 1).map (fun c => (9150136321-1+2*2^10*c.k,115775135290938+c.lower,115775524773366+c.upper)) = pointBounds69780 := by
 decide +kernel
def cuts69781 : List PrefixCut := [⟨64,177153555,177153656⟩]
theorem checked69781 : checkPrefixCuts (2^48) 9150267393 10 Manual.Count131072.C069781.packed 64 cuts69781 = true := by
 decide +kernel
def cuts69782 : List PrefixCut := [⟨50,136547063,136547144⟩,
⟨64,172659949,172660053⟩]
theorem checked69782 : checkPrefixCuts (2^48) 9150398465 10 Manual.Count131072.C069782.packed 64 cuts69782 = true := by
 decide +kernel
def pointBounds69782 : List (Nat × Nat × Nat) := [(9150500864,115775622794633,115776012277343)]
theorem point_links_checked69782 : (cuts69782.take 1).map (fun c => (9150398465-1+2*2^10*c.k,115775486247570+c.lower,115775875730199+c.upper)) = pointBounds69782 := by
 decide +kernel
def cuts69783 : List PrefixCut := [⟨64,179732323,179732432⟩]
theorem checked69783 : checkPrefixCuts (2^48) 9150529537 10 Manual.Count131072.C069783.packed 64 cuts69783 = true := by
 decide +kernel
def cuts69784 : List PrefixCut := [⟨62,170624889,170624992⟩,
⟨64,175823266,175823373⟩]
theorem checked69784 : checkPrefixCuts (2^48) 9150660609 10 Manual.Count131072.C069784.packed 64 cuts69784 = true := by
 decide +kernel
def pointBounds69784 : List (Nat × Nat × Nat) := [(9150787584,115776009264731,115776398747676)]
theorem point_links_checked69784 : (cuts69784.take 1).map (fun c => (9150660609-1+2*2^10*c.k,115775838639842+c.lower,115776228122684+c.upper)) = pointBounds69784 := by
 decide +kernel
def cuts69785 : List PrefixCut := [⟨64,175420876,175420980⟩]
theorem checked69785 : checkPrefixCuts (2^48) 9150791681 10 Manual.Count131072.C069785.packed 64 cuts69785 = true := by
 decide +kernel
def cuts69786 : List PrefixCut := [⟨64,174956971,174957073⟩]
theorem checked69786 : checkPrefixCuts (2^48) 9150922753 10 Manual.Count131072.C069786.packed 64 cuts69786 = true := by
 decide +kernel
def cuts69787 : List PrefixCut := [⟨10,27621318,27621333⟩,
⟨64,173970199,173970306⟩]
theorem checked69787 : checkPrefixCuts (2^48) 9151053825 10 Manual.Count131072.C069787.packed 64 cuts69787 = true := by
 decide +kernel
def pointBounds69787 : List (Nat × Nat × Nat) := [(9151074304,115776392462273,115776781945443)]
theorem point_links_checked69787 : (cuts69787.take 1).map (fun c => (9151053825-1+2*2^10*c.k,115776364840955+c.lower,115776754324110+c.upper)) = pointBounds69787 := by
 decide +kernel
def cuts69788 : List PrefixCut := [⟨64,177166534,177166641⟩]
theorem checked69788 : checkPrefixCuts (2^48) 9151184897 10 Manual.Count131072.C069788.packed 64 cuts69788 = true := by
 decide +kernel
def cuts69789 : List PrefixCut := [⟨22,60562076,60562114⟩,
⟨64,175933707,175933813⟩]
theorem checked69789 : checkPrefixCuts (2^48) 9151315969 10 Manual.Count131072.C069789.packed 64 cuts69789 = true := by
 decide +kernel
def pointBounds69789 : List (Nat × Nat × Nat) := [(9151361024,115776776539764,115777166023171)]
theorem point_links_checked69789 : (cuts69789.take 1).map (fun c => (9151315969-1+2*2^10*c.k,115776715977688+c.lower,115777105461057+c.upper)) = pointBounds69789 := by
 decide +kernel
def cuts69790 : List PrefixCut := [⟨64,176392527,176392638⟩]
theorem checked69790 : checkPrefixCuts (2^48) 9151447041 10 Manual.Count131072.C069790.packed 64 cuts69790 = true := by
 decide +kernel
def cuts69791 : List PrefixCut := [⟨34,95192486,95192544⟩,
⟨64,178358439,178358550⟩]
theorem checked69791 : checkPrefixCuts (2^48) 9151578113 10 Manual.Count131072.C069791.packed 64 cuts69791 = true := by
 decide +kernel
def pointBounds69791 : List (Nat × Nat × Nat) := [(9151647744,115777163496408,115777552980052)]
theorem point_links_checked69791 : (cuts69791.take 1).map (fun c => (9151578113-1+2*2^10*c.k,115777068303922+c.lower,115777457787508+c.upper)) = pointBounds69791 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000305
