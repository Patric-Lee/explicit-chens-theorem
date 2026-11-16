import PlattAssemblyKernel
import PlattCertificates.Count131072.C065760
import PlattCertificates.Count131072.C065761
import PlattCertificates.Count131072.C065762
import PlattCertificates.Count131072.C065763
import PlattCertificates.Count131072.C065764
import PlattCertificates.Count131072.C065765
import PlattCertificates.Count131072.C065766
import PlattCertificates.Count131072.C065767
import PlattCertificates.Count131072.C065768
import PlattCertificates.Count131072.C065769
import PlattCertificates.Count131072.C065770
import PlattCertificates.Count131072.C065771
import PlattCertificates.Count131072.C065772
import PlattCertificates.Count131072.C065773
import PlattCertificates.Count131072.C065774
import PlattCertificates.Count131072.C065775
import PlattCertificates.Count131072.C065776
import PlattCertificates.Count131072.C065777
import PlattCertificates.Count131072.C065778
import PlattCertificates.Count131072.C065779
import PlattCertificates.Count131072.C065780
import PlattCertificates.Count131072.C065781
import PlattCertificates.Count131072.C065782
import PlattCertificates.Count131072.C065783
import PlattCertificates.Count131072.C065784
import PlattCertificates.Count131072.C065785
import PlattCertificates.Count131072.C065786
import PlattCertificates.Count131072.C065787
import PlattCertificates.Count131072.C065788
import PlattCertificates.Count131072.C065789
import PlattCertificates.Count131072.C065790
import PlattCertificates.Count131072.C065791
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000180
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts65760 : List PrefixCut := [⟨35,100763833,100763889⟩,
⟨64,184912580,184912685⟩]
theorem checked65760 : checkPrefixCuts (2^48) 8623226881 10 Manual.Count131072.C065760.packed 64 cuts65760 = true := by
 decide +kernel
def pointBounds65760 : List (Nat × Nat × Nat) := [(8623298560,115046518557442,115046907614481)]
theorem point_links_checked65760 : (cuts65760.take 1).map (fun c => (8623226881-1+2*2^10*c.k,115046417793609+c.lower,115046806850592+c.upper)) = pointBounds65760 := by
 decide +kernel
def cuts65761 : List PrefixCut := [⟨64,185334104,185334212⟩]
theorem checked65761 : checkPrefixCuts (2^48) 8623357953 10 Manual.Count131072.C065761.packed 64 cuts65761 = true := by
 decide +kernel
def cuts65762 : List PrefixCut := [⟨39,113196690,113196758⟩,
⟨64,184613205,184613314⟩]
theorem checked65762 : checkPrefixCuts (2^48) 8623489025 10 Manual.Count131072.C065762.packed 64 cuts65762 = true := by
 decide +kernel
def pointBounds65762 : List (Nat × Nat × Nat) := [(8623568896,115046901236983,115047290294247)]
theorem point_links_checked65762 : (cuts65762.take 1).map (fun c => (8623489025-1+2*2^10*c.k,115046788040293+c.lower,115047177097489+c.upper)) = pointBounds65762 := by
 decide +kernel
def cuts65763 : List PrefixCut := [⟨64,188951473,188951583⟩]
theorem checked65763 : checkPrefixCuts (2^48) 8623620097 10 Manual.Count131072.C065763.packed 64 cuts65763 = true := by
 decide +kernel
def cuts65764 : List PrefixCut := [⟨43,128044094,128044168⟩,
⟨64,186761806,186761912⟩]
theorem checked65764 : checkPrefixCuts (2^48) 8623751169 10 Manual.Count131072.C065764.packed 64 cuts65764 = true := by
 decide +kernel
def pointBounds65764 : List (Nat × Nat × Nat) := [(8623839232,115047289649065,115047678706554)]
theorem point_links_checked65764 : (cuts65764.take 1).map (fun c => (8623751169-1+2*2^10*c.k,115047161604971+c.lower,115047550662386+c.upper)) = pointBounds65764 := by
 decide +kernel
def cuts65765 : List PrefixCut := [⟨64,185029081,185029183⟩]
theorem checked65765 : checkPrefixCuts (2^48) 8623882241 10 Manual.Count131072.C065765.packed 64 cuts65765 = true := by
 decide +kernel
def cuts65766 : List PrefixCut := [⟨47,135285850,135285921⟩,
⟨64,185124188,185124290⟩]
theorem checked65766 : checkPrefixCuts (2^48) 8624013313 10 Manual.Count131072.C065766.packed 64 cuts65766 = true := by
 decide +kernel
def pointBounds65766 : List (Nat × Nat × Nat) := [(8624109568,115047668681708,115048057739402)]
theorem point_links_checked65766 : (cuts65766.take 1).map (fun c => (8624013313-1+2*2^10*c.k,115047533395858+c.lower,115047922453481+c.upper)) = pointBounds65766 := by
 decide +kernel
def cuts65767 : List PrefixCut := [⟨64,185545662,185545769⟩]
theorem checked65767 : checkPrefixCuts (2^48) 8624144385 10 Manual.Count131072.C065767.packed 64 cuts65767 = true := by
 decide +kernel
def cuts65768 : List PrefixCut := [⟨51,151371868,151371956⟩,
⟨64,190340524,190340634⟩]
theorem checked65768 : checkPrefixCuts (2^48) 8624275457 10 Manual.Count131072.C065768.packed 64 cuts65768 = true := by
 decide +kernel
def pointBounds65768 : List (Nat × Nat × Nat) := [(8624379904,115048055437576,115048444495496)]
theorem point_links_checked65768 : (cuts65768.take 1).map (fun c => (8624275457-1+2*2^10*c.k,115047904065708+c.lower,115048293123540+c.upper)) = pointBounds65768 := by
 decide +kernel
def cuts65769 : List PrefixCut := [⟨64,185213653,185213762⟩]
theorem checked65769 : checkPrefixCuts (2^48) 8624406529 10 Manual.Count131072.C065769.packed 64 cuts65769 = true := by
 decide +kernel
def cuts65770 : List PrefixCut := [⟨55,162626721,162626814⟩,
⟨64,189649378,189649486⟩]
theorem checked65770 : checkPrefixCuts (2^48) 8624537601 10 Manual.Count131072.C065770.packed 64 cuts65770 = true := by
 decide +kernel
def pointBounds65770 : List (Nat × Nat × Nat) := [(8624650240,115048442246606,115048831304750)]
theorem point_links_checked65770 : (cuts65770.take 1).map (fun c => (8624537601-1+2*2^10*c.k,115048279619885+c.lower,115048668677936+c.upper)) = pointBounds65770 := by
 decide +kernel
def cuts65771 : List PrefixCut := [⟨64,188700054,188700163⟩]
theorem checked65771 : checkPrefixCuts (2^48) 8624668673 10 Manual.Count131072.C065771.packed 64 cuts65771 = true := by
 decide +kernel
def cuts65772 : List PrefixCut := [⟨59,171008962,171009063⟩,
⟨64,186771692,186771802⟩]
theorem checked65772 : checkPrefixCuts (2^48) 8624799745 10 Manual.Count131072.C065772.packed 64 cuts65772 = true := by
 decide +kernel
def pointBounds65772 : List (Nat × Nat × Nat) := [(8624920576,115048828978279,115049218036648)]
theorem point_links_checked65772 : (cuts65772.take 1).map (fun c => (8624799745-1+2*2^10*c.k,115048657969317+c.lower,115049047027585+c.upper)) = pointBounds65772 := by
 decide +kernel
def cuts65773 : List PrefixCut := [⟨64,186540437,186540551⟩]
theorem checked65773 : checkPrefixCuts (2^48) 8624930817 10 Manual.Count131072.C065773.packed 64 cuts65773 = true := by
 decide +kernel
def cuts65774 : List PrefixCut := [⟨63,183404727,183404836⟩,
⟨64,186700766,186700876⟩]
theorem checked65774 : checkPrefixCuts (2^48) 8625061889 10 Manual.Count131072.C065774.packed 64 cuts65774 = true := by
 decide +kernel
def pointBounds65774 : List (Nat × Nat × Nat) := [(8625190912,115049214686173,115049603744774)]
theorem point_links_checked65774 : (cuts65774.take 1).map (fun c => (8625061889-1+2*2^10*c.k,115049031281446+c.lower,115049420339938+c.upper)) = pointBounds65774 := by
 decide +kernel
def cuts65775 : List PrefixCut := [⟨64,186306326,186306439⟩]
theorem checked65775 : checkPrefixCuts (2^48) 8625192961 10 Manual.Count131072.C065775.packed 64 cuts65775 = true := by
 decide +kernel
def cuts65776 : List PrefixCut := [⟨64,186629832,186629944⟩]
theorem checked65776 : checkPrefixCuts (2^48) 8625324033 10 Manual.Count131072.C065776.packed 64 cuts65776 = true := by
 decide +kernel
def cuts65777 : List PrefixCut := [⟨3,9137251,9137255⟩,
⟨64,186137505,186137612⟩]
theorem checked65777 : checkPrefixCuts (2^48) 8625455105 10 Manual.Count131072.C065777.packed 64 cuts65777 = true := by
 decide +kernel
def pointBounds65777 : List (Nat × Nat × Nat) := [(8625461248,115049600055621,115049989114452)]
theorem point_links_checked65777 : (cuts65777.take 1).map (fun c => (8625455105-1+2*2^10*c.k,115049590918370+c.lower,115049979977197+c.upper)) = pointBounds65777 := by
 decide +kernel
def cuts65778 : List PrefixCut := [⟨64,188321016,188321125⟩]
theorem checked65778 : checkPrefixCuts (2^48) 8625586177 10 Manual.Count131072.C065778.packed 64 cuts65778 = true := by
 decide +kernel
def cuts65779 : List PrefixCut := [⟨7,20590811,20590822⟩,
⟨64,187012908,187013016⟩]
theorem checked65779 : checkPrefixCuts (2^48) 8625717249 10 Manual.Count131072.C065779.packed 64 cuts65779 = true := by
 decide +kernel
def pointBounds65779 : List (Nat × Nat × Nat) := [(8625731584,115049985967702,115050375026756)]
theorem point_links_checked65779 : (cuts65779.take 1).map (fun c => (8625717249-1+2*2^10*c.k,115049965376891+c.lower,115050354435934+c.upper)) = pointBounds65779 := by
 decide +kernel
def cuts65780 : List PrefixCut := [⟨64,189555303,189555409⟩]
theorem checked65780 : checkPrefixCuts (2^48) 8625848321 10 Manual.Count131072.C065780.packed 64 cuts65780 = true := by
 decide +kernel
def cuts65781 : List PrefixCut := [⟨11,31717354,31717372⟩,
⟨64,185930405,185930514⟩]
theorem checked65781 : checkPrefixCuts (2^48) 8625979393 10 Manual.Count131072.C065781.packed 64 cuts65781 = true := by
 decide +kernel
def pointBounds65781 : List (Nat × Nat × Nat) := [(8626001920,115050373662456,115050762721731)]
theorem point_links_checked65781 : (cuts65781.take 1).map (fun c => (8625979393-1+2*2^10*c.k,115050341945102+c.lower,115050731004359+c.upper)) = pointBounds65781 := by
 decide +kernel
def cuts65782 : List PrefixCut := [⟨64,187722237,187722354⟩]
theorem checked65782 : checkPrefixCuts (2^48) 8626110465 10 Manual.Count131072.C065782.packed 64 cuts65782 = true := by
 decide +kernel
def cuts65783 : List PrefixCut := [⟨15,43300031,43300055⟩,
⟨64,187621500,187621605⟩]
theorem checked65783 : checkPrefixCuts (2^48) 8626241537 10 Manual.Count131072.C065783.packed 64 cuts65783 = true := by
 decide +kernel
def pointBounds65783 : List (Nat × Nat × Nat) := [(8626272256,115050758897775,115051147957282)]
theorem point_links_checked65783 : (cuts65783.take 1).map (fun c => (8626241537-1+2*2^10*c.k,115050715597744+c.lower,115051104657227+c.upper)) = pointBounds65783 := by
 decide +kernel
def cuts65784 : List PrefixCut := [⟨64,187716528,187716629⟩]
theorem checked65784 : checkPrefixCuts (2^48) 8626372609 10 Manual.Count131072.C065784.packed 64 cuts65784 = true := by
 decide +kernel
def cuts65785 : List PrefixCut := [⟨19,55371427,55371459⟩,
⟨64,184679204,184679312⟩]
theorem checked65785 : checkPrefixCuts (2^48) 8626503681 10 Manual.Count131072.C065785.packed 64 cuts65785 = true := by
 decide +kernel
def pointBounds65785 : List (Nat × Nat × Nat) := [(8626542592,115051146307199,115051535366920)]
theorem point_links_checked65785 : (cuts65785.take 1).map (fun c => (8626503681-1+2*2^10*c.k,115051090935772+c.lower,115051479995461+c.upper)) = pointBounds65785 := by
 decide +kernel
def cuts65786 : List PrefixCut := [⟨64,187710816,187710925⟩]
theorem checked65786 : checkPrefixCuts (2^48) 8626634753 10 Manual.Count131072.C065786.packed 64 cuts65786 = true := by
 decide +kernel
def cuts65787 : List PrefixCut := [⟨23,66952654,66952694⟩,
⟨64,184673589,184673697⟩]
theorem checked65787 : checkPrefixCuts (2^48) 8626765825 10 Manual.Count131072.C065787.packed 64 cuts65787 = true := by
 decide +kernel
def pointBounds65787 : List (Nat × Nat × Nat) := [(8626812928,115051530278446,115051919338392)]
theorem point_links_checked65787 : (cuts65787.take 1).map (fun c => (8626765825-1+2*2^10*c.k,115051463325792+c.lower,115051852385698+c.upper)) = pointBounds65787 := by
 decide +kernel
def cuts65788 : List PrefixCut := [⟨64,186530545,186530654⟩]
theorem checked65788 : checkPrefixCuts (2^48) 8626896897 10 Manual.Count131072.C065788.packed 64 cuts65788 = true := by
 decide +kernel
def cuts65789 : List PrefixCut := [⟨27,79577241,79577283⟩,
⟨64,188583200,188583306⟩]
theorem checked65789 : checkPrefixCuts (2^48) 8627027969 10 Manual.Count131072.C065789.packed 64 cuts65789 = true := by
 decide +kernel
def pointBounds65789 : List (Nat × Nat × Nat) := [(8627083264,115051914107167,115052303167332)]
theorem point_links_checked65789 : (cuts65789.take 1).map (fun c => (8627027969-1+2*2^10*c.k,115051834529926+c.lower,115052223590049+c.upper)) = pointBounds65789 := by
 decide +kernel
def cuts65790 : List PrefixCut := [⟨64,184632552,184632660⟩]
theorem checked65790 : checkPrefixCuts (2^48) 8627159041 10 Manual.Count131072.C065790.packed 64 cuts65790 = true := by
 decide +kernel
def cuts65791 : List PrefixCut := [⟨31,92135791,92135840⟩,
⟨64,188740602,188740707⟩]
theorem checked65791 : checkPrefixCuts (2^48) 8627290113 10 Manual.Count131072.C065791.packed 64 cuts65791 = true := by
 decide +kernel
def pointBounds65791 : List (Nat × Nat × Nat) := [(8627353600,115052299881469,115052688941855)]
theorem point_links_checked65791 : (cuts65791.take 1).map (fun c => (8627290113-1+2*2^10*c.k,115052207745678+c.lower,115052596806015+c.upper)) = pointBounds65791 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000180
