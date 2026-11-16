import PlattAssemblyKernel
import PlattCertificates.Count131072.C046816
import PlattCertificates.Count131072.C046817
import PlattCertificates.Count131072.C046818
import PlattCertificates.Count131072.C046819
import PlattCertificates.Count131072.C046820
import PlattCertificates.Count131072.C046821
import PlattCertificates.Count131072.C046822
import PlattCertificates.Count131072.C046823
import PlattCertificates.Count131072.C046824
import PlattCertificates.Count131072.C046825
import PlattCertificates.Count131072.C046826
import PlattCertificates.Count131072.C046827
import PlattCertificates.Count131072.C046828
import PlattCertificates.Count131072.C046829
import PlattCertificates.Count131072.C046830
import PlattCertificates.Count131072.C046831
import PlattCertificates.Count131072.C046832
import PlattCertificates.Count131072.C046833
import PlattCertificates.Count131072.C046834
import PlattCertificates.Count131072.C046835
import PlattCertificates.Count131072.C046836
import PlattCertificates.Count131072.C046837
import PlattCertificates.Count131072.C046838
import PlattCertificates.Count131072.C046839
import PlattCertificates.Count131072.C046840
import PlattCertificates.Count131072.C046841
import PlattCertificates.Count131072.C046842
import PlattCertificates.Count131072.C046843
import PlattCertificates.Count131072.C046844
import PlattCertificates.Count131072.C046845
import PlattCertificates.Count131072.C046846
import PlattCertificates.Count131072.C046847
namespace ChenEffective.PlattWindow.Assembly.Prefix.S5.B000213
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts46816 : List PrefixCut := [⟨64,267297924,267298075⟩]
theorem checked46816 : checkPrefixCuts (2^48) 6140198913 10 Manual.Count131072.C046816.packed 64 cuts46816 = true := by
 decide +kernel
def cuts46817 : List PrefixCut := [⟨18,75957238,75957279⟩,
⟨64,265779542,265779695⟩]
theorem checked46817 : checkPrefixCuts (2^48) 6140329985 10 Manual.Count131072.C046817.packed 64 cuts46817 = true := by
 decide +kernel
def pointBounds46817 : List (Nat × Nat × Nat) := [(6140366848,110837184483649,110837571137288)]
theorem point_links_checked46817 : (cuts46817.take 1).map (fun c => (6140329985-1+2*2^10*c.k,110837108526411+c.lower,110837495180009+c.upper)) = pointBounds46817 := by
 decide +kernel
def cuts46818 : List PrefixCut := [⟨48,199812241,199812353⟩,
⟨64,264857101,264857248⟩]
theorem checked46818 : checkPrefixCuts (2^48) 6140461057 10 Manual.Count131072.C046818.packed 64 cuts46818 = true := by
 decide +kernel
def pointBounds46818 : List (Nat × Nat × Nat) := [(6140559360,110837574118194,110837960772057)]
theorem point_links_checked46818 : (cuts46818.take 1).map (fun c => (6140461057-1+2*2^10*c.k,110837374305953+c.lower,110837760959704+c.upper)) = pointBounds46818 := by
 decide +kernel
def cuts46819 : List PrefixCut := [⟨64,269801914,269802068⟩]
theorem checked46819 : checkPrefixCuts (2^48) 6140592129 10 Manual.Count131072.C046819.packed 64 cuts46819 = true := by
 decide +kernel
def cuts46820 : List PrefixCut := [⟨14,59267643,59267677⟩,
⟨64,266633427,266633576⟩]
theorem checked46820 : checkPrefixCuts (2^48) 6140723201 10 Manual.Count131072.C046820.packed 64 cuts46820 = true := by
 decide +kernel
def pointBounds46820 : List (Nat × Nat × Nat) := [(6140751872,110837968232611,110838354886697)]
theorem point_links_checked46820 : (cuts46820.take 1).map (fun c => (6140723201-1+2*2^10*c.k,110837908964968+c.lower,110838295619020+c.upper)) = pointBounds46820 := by
 decide +kernel
def cuts46821 : List PrefixCut := [⟨44,180823432,180823535⟩,
⟨64,265573484,265573636⟩]
theorem checked46821 : checkPrefixCuts (2^48) 6140854273 10 Manual.Count131072.C046821.packed 64 cuts46821 = true := by
 decide +kernel
def pointBounds46821 : List (Nat × Nat × Nat) := [(6140944384,110838356421827,110838743076131)]
theorem point_links_checked46821 : (cuts46821.take 1).map (fun c => (6140854273-1+2*2^10*c.k,110838175598395+c.lower,110838562252596+c.upper)) = pointBounds46821 := by
 decide +kernel
def cuts46822 : List PrefixCut := [⟨64,265522020,265522177⟩]
theorem checked46822 : checkPrefixCuts (2^48) 6140985345 10 Manual.Count131072.C046822.packed 64 cuts46822 = true := by
 decide +kernel
def cuts46823 : List PrefixCut := [⟨10,40196775,40196799⟩,
⟨64,270512199,270512349⟩]
theorem checked46823 : checkPrefixCuts (2^48) 6141116417 10 Manual.Count131072.C046823.packed 64 cuts46823 = true := by
 decide +kernel
def pointBounds46823 : List (Nat × Nat × Nat) := [(6141136896,110838746890674,110839133545208)]
theorem point_links_checked46823 : (cuts46823.take 1).map (fun c => (6141116417-1+2*2^10*c.k,110838706693899+c.lower,110839093348409+c.upper)) = pointBounds46823 := by
 decide +kernel
def cuts46824 : List PrefixCut := [⟨40,165137010,165137101⟩,
⟨64,263173178,263173325⟩]
theorem checked46824 : checkPrefixCuts (2^48) 6141247489 10 Manual.Count131072.C046824.packed 64 cuts46824 = true := by
 decide +kernel
def pointBounds46824 : List (Nat × Nat × Nat) := [(6141329408,110839142343108,110839528997859)]
theorem point_links_checked46824 : (cuts46824.take 1).map (fun c => (6141247489-1+2*2^10*c.k,110838977206098+c.lower,110839363860758+c.upper)) = pointBounds46824 := by
 decide +kernel
def cuts46825 : List PrefixCut := [⟨64,266513325,266513480⟩]
theorem checked46825 : checkPrefixCuts (2^48) 6141378561 10 Manual.Count131072.C046825.packed 64 cuts46825 = true := by
 decide +kernel
def cuts46826 : List PrefixCut := [⟨6,24932339,24932352⟩,
⟨64,261878678,261878826⟩]
theorem checked46826 : checkPrefixCuts (2^48) 6141509633 10 Manual.Count131072.C046826.packed 64 cuts46826 = true := by
 decide +kernel
def pointBounds46826 : List (Nat × Nat × Nat) := [(6141521920,110839531824940,110839918479915)]
theorem point_links_checked46826 : (cuts46826.take 1).map (fun c => (6141509633-1+2*2^10*c.k,110839506892601+c.lower,110839893547563+c.upper)) = pointBounds46826 := by
 decide +kernel
def cuts46827 : List PrefixCut := [⟨36,151560789,151560871⟩,
⟨64,268747595,268747748⟩]
theorem checked46827 : checkPrefixCuts (2^48) 6141640705 10 Manual.Count131072.C046827.packed 64 cuts46827 = true := by
 decide +kernel
def pointBounds46827 : List (Nat × Nat × Nat) := [(6141714432,110839920332068,110840306987260)]
theorem point_links_checked46827 : (cuts46827.take 1).map (fun c => (6141640705-1+2*2^10*c.k,110839768771279+c.lower,110840155426389+c.upper)) = pointBounds46827 := by
 decide +kernel
def cuts46828 : List PrefixCut := [⟨64,269245973,269246131⟩]
theorem checked46828 : checkPrefixCuts (2^48) 6141771777 10 Manual.Count131072.C046828.packed 64 cuts46828 = true := by
 decide +kernel
def cuts46829 : List PrefixCut := [⟨2,8065833,8065838⟩,
⟨64,268461154,268461307⟩]
theorem checked46829 : checkPrefixCuts (2^48) 6141902849 10 Manual.Count131072.C046829.packed 64 cuts46829 = true := by
 decide +kernel
def pointBounds46829 : List (Nat × Nat × Nat) := [(6141906944,110840314830680,110840701486106)]
theorem point_links_checked46829 : (cuts46829.take 1).map (fun c => (6141902849-1+2*2^10*c.k,110840306764847+c.lower,110840693420268+c.upper)) = pointBounds46829 := by
 decide +kernel
def cuts46830 : List PrefixCut := [⟨32,133815986,133816063⟩,
⟨64,268547076,268547230⟩]
theorem checked46830 : checkPrefixCuts (2^48) 6142033921 10 Manual.Count131072.C046830.packed 64 cuts46830 = true := by
 decide +kernel
def pointBounds46830 : List (Nat × Nat × Nat) := [(6142099456,110840709041987,110841095697638)]
theorem point_links_checked46830 : (cuts46830.take 1).map (fun c => (6142033921-1+2*2^10*c.k,110840575226001+c.lower,110840961881575+c.upper)) = pointBounds46830 := by
 decide +kernel
def cuts46831 : List PrefixCut := [⟨62,258780467,258780615⟩,
⟨64,267074918,267075071⟩]
theorem checked46831 : checkPrefixCuts (2^48) 6142164993 10 Manual.Count131072.C046831.packed 64 cuts46831 = true := by
 decide +kernel
def pointBounds46831 : List (Nat × Nat × Nat) := [(6142291968,110841102553544,110841489209420)]
theorem point_links_checked46831 : (cuts46831.take 1).map (fun c => (6142164993-1+2*2^10*c.k,110840843773077+c.lower,110841230428805+c.upper)) = pointBounds46831 := by
 decide +kernel
def cuts46832 : List PrefixCut := [⟨64,266381822,266381980⟩]
theorem checked46832 : checkPrefixCuts (2^48) 6142296065 10 Manual.Count131072.C046832.packed 64 cuts46832 = true := by
 decide +kernel
def cuts46833 : List PrefixCut := [⟨28,120243453,120243521⟩,
⟨64,271279364,271279516⟩]
theorem checked46833 : checkPrefixCuts (2^48) 6142427137 10 Manual.Count131072.C046833.packed 64 cuts46833 = true := by
 decide +kernel
def pointBounds46833 : List (Nat × Nat × Nat) := [(6142484480,110841497473270,110841884129377)]
theorem point_links_checked46833 : (cuts46833.take 1).map (fun c => (6142427137-1+2*2^10*c.k,110841377229817+c.lower,110841763885856+c.upper)) = pointBounds46833 := by
 decide +kernel
def cuts46834 : List PrefixCut := [⟨58,242634287,242634426⟩,
⟨64,267791002,267791154⟩]
theorem checked46834 : checkPrefixCuts (2^48) 6142558209 10 Manual.Count131072.C046834.packed 64 cuts46834 = true := by
 decide +kernel
def pointBounds46834 : List (Nat × Nat × Nat) := [(6142676992,110841891143468,110842277799798)]
theorem point_links_checked46834 : (cuts46834.take 1).map (fun c => (6142558209-1+2*2^10*c.k,110841648509181+c.lower,110842035165372+c.upper)) = pointBounds46834 := by
 decide +kernel
def cuts46835 : List PrefixCut := [⟨64,265769066,265769221⟩]
theorem checked46835 : checkPrefixCuts (2^48) 6142689281 10 Manual.Count131072.C046835.packed 64 cuts46835 = true := by
 decide +kernel
def cuts46836 : List PrefixCut := [⟨24,99387021,99387074⟩,
⟨64,266267460,266267610⟩]
theorem checked46836 : checkPrefixCuts (2^48) 6142820353 10 Manual.Count131072.C046836.packed 64 cuts46836 = true := by
 decide +kernel
def pointBounds46836 : List (Nat × Nat × Nat) := [(6142869504,110842281456270,110842668112821)]
theorem point_links_checked46836 : (cuts46836.take 1).map (fun c => (6142820353-1+2*2^10*c.k,110842182069249+c.lower,110842568725747+c.upper)) = pointBounds46836 := by
 decide +kernel
def cuts46837 : List PrefixCut := [⟨54,225482080,225482210⟩,
⟨64,268690239,268690390⟩]
theorem checked46837 : checkPrefixCuts (2^48) 6142951425 10 Manual.Count131072.C046837.packed 64 cuts46837 = true := by
 decide +kernel
def pointBounds46837 : List (Nat × Nat × Nat) := [(6143062016,110842673818789,110843060475567)]
theorem point_links_checked46837 : (cuts46837.take 1).map (fun c => (6142951425-1+2*2^10*c.k,110842448336709+c.lower,110842834993357+c.upper)) = pointBounds46837 := by
 decide +kernel
def cuts46838 : List PrefixCut := [⟨64,268501254,268501408⟩]
theorem checked46838 : checkPrefixCuts (2^48) 6143082497 10 Manual.Count131072.C046838.packed 64 cuts46838 = true := by
 decide +kernel
def cuts46839 : List PrefixCut := [⟨20,82702730,82702778⟩,
⟨64,265929692,265929843⟩]
theorem checked46839 : checkPrefixCuts (2^48) 6143213569 10 Manual.Count131072.C046839.packed 64 cuts46839 = true := by
 decide +kernel
def pointBounds46839 : List (Nat × Nat × Nat) := [(6143254528,110843068230932,110843454887933)]
theorem point_links_checked46839 : (cuts46839.take 1).map (fun c => (6143213569-1+2*2^10*c.k,110842985528202+c.lower,110843372185155+c.upper)) = pointBounds46839 := by
 decide +kernel
def cuts46840 : List PrefixCut := [⟨50,212226568,212226684⟩,
⟨64,268810548,268810698⟩]
theorem checked46840 : checkPrefixCuts (2^48) 6143344641 10 Manual.Count131072.C046840.packed 64 cuts46840 = true := by
 decide +kernel
def pointBounds46840 : List (Nat × Nat × Nat) := [(6143447040,110843463684462,110843850341682)]
theorem point_links_checked46840 : (cuts46840.take 1).map (fun c => (6143344641-1+2*2^10*c.k,110843251457894+c.lower,110843638114998+c.upper)) = pointBounds46840 := by
 decide +kernel
def cuts46841 : List PrefixCut := [⟨64,269629495,269629645⟩]
theorem checked46841 : checkPrefixCuts (2^48) 6143475713 10 Manual.Count131072.C046841.packed 64 cuts46841 = true := by
 decide +kernel
def cuts46842 : List PrefixCut := [⟨16,67440833,67440872⟩,
⟨64,268386693,268386847⟩]
theorem checked46842 : checkPrefixCuts (2^48) 6143606785 10 Manual.Count131072.C046842.packed 64 cuts46842 = true := by
 decide +kernel
def pointBounds46842 : List (Nat × Nat × Nat) := [(6143639552,110843857338770,110844243996213)]
theorem point_links_checked46842 : (cuts46842.take 1).map (fun c => (6143606785-1+2*2^10*c.k,110843789897937+c.lower,110844176555341+c.upper)) = pointBounds46842 := by
 decide +kernel
def cuts46843 : List PrefixCut := [⟨46,192604474,192604581⟩,
⟨64,269892838,269892988⟩]
theorem checked46843 : checkPrefixCuts (2^48) 6143737857 10 Manual.Count131072.C046843.packed 64 cuts46843 = true := by
 decide +kernel
def pointBounds46843 : List (Nat × Nat × Nat) := [(6143832064,110844250889104,110844637546769)]
theorem point_links_checked46843 : (cuts46843.take 1).map (fun c => (6143737857-1+2*2^10*c.k,110844058284630+c.lower,110844444942188+c.upper)) = pointBounds46843 := by
 decide +kernel
def cuts46844 : List PrefixCut := [⟨64,263152525,263152671⟩]
theorem checked46844 : checkPrefixCuts (2^48) 6143868929 10 Manual.Count131072.C046844.packed 64 cuts46844 = true := by
 decide +kernel
def cuts46845 : List PrefixCut := [⟨12,50898108,50898137⟩,
⟨64,265300102,265300252⟩]
theorem checked46845 : checkPrefixCuts (2^48) 6144000001 10 Manual.Count131072.C046845.packed 64 cuts46845 = true := by
 decide +kernel
def pointBounds46845 : List (Nat × Nat × Nat) := [(6144024576,110844642228101,110845028885984)]
theorem point_links_checked46845 : (cuts46845.take 1).map (fun c => (6144000001-1+2*2^10*c.k,110844591329993+c.lower,110844977987847+c.upper)) = pointBounds46845 := by
 decide +kernel
def cuts46846 : List PrefixCut := [⟨42,171931209,171931306⟩,
⟨64,263920065,263920216⟩]
theorem checked46846 : checkPrefixCuts (2^48) 6144131073 10 Manual.Count131072.C046846.packed 64 cuts46846 = true := by
 decide +kernel
def pointBounds46846 : List (Nat × Nat × Nat) := [(6144217088,110845028561304,110845415219405)]
theorem point_links_checked46846 : (cuts46846.take 1).map (fun c => (6144131073-1+2*2^10*c.k,110844856630095+c.lower,110845243288099+c.upper)) = pointBounds46846 := by
 decide +kernel
def cuts46847 : List PrefixCut := [⟨64,267670903,267671056⟩]
theorem checked46847 : checkPrefixCuts (2^48) 6144262145 10 Manual.Count131072.C046847.packed 64 cuts46847 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S5.B000213
