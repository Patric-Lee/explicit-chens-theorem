import PlattAssemblyKernel
import PlattCertificates.Count131072.C069792
import PlattCertificates.Count131072.C069793
import PlattCertificates.Count131072.C069794
import PlattCertificates.Count131072.C069795
import PlattCertificates.Count131072.C069796
import PlattCertificates.Count131072.C069797
import PlattCertificates.Count131072.C069798
import PlattCertificates.Count131072.C069799
import PlattCertificates.Count131072.C069800
import PlattCertificates.Count131072.C069801
import PlattCertificates.Count131072.C069802
import PlattCertificates.Count131072.C069803
import PlattCertificates.Count131072.C069804
import PlattCertificates.Count131072.C069805
import PlattCertificates.Count131072.C069806
import PlattCertificates.Count131072.C069807
import PlattCertificates.Count131072.C069808
import PlattCertificates.Count131072.C069809
import PlattCertificates.Count131072.C069810
import PlattCertificates.Count131072.C069811
import PlattCertificates.Count131072.C069812
import PlattCertificates.Count131072.C069813
import PlattCertificates.Count131072.C069814
import PlattCertificates.Count131072.C069815
import PlattCertificates.Count131072.C069816
import PlattCertificates.Count131072.C069817
import PlattCertificates.Count131072.C069818
import PlattCertificates.Count131072.C069819
import PlattCertificates.Count131072.C069820
import PlattCertificates.Count131072.C069821
import PlattCertificates.Count131072.C069822
import PlattCertificates.Count131072.C069823
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000306
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts69792 : List PrefixCut := [⟨64,174511356,174511464⟩]
theorem checked69792 : checkPrefixCuts (2^48) 9151709185 10 Manual.Count131072.C069792.packed 64 cuts69792 = true := by
 decide +kernel
def cuts69793 : List PrefixCut := [⟨46,126068582,126068659⟩,
⟨64,174293549,174293658⟩]
theorem checked69793 : checkPrefixCuts (2^48) 9151840257 10 Manual.Count131072.C069793.packed 64 cuts69793 = true := by
 decide +kernel
def pointBounds69793 : List (Nat × Nat × Nat) := [(9151934464,115777547242299,115777936726181)]
theorem point_links_checked69793 : (cuts69793.take 1).map (fun c => (9151840257-1+2*2^10*c.k,115777421173717+c.lower,115777810657522+c.upper)) = pointBounds69793 := by
 decide +kernel
def cuts69794 : List PrefixCut := [⟨64,174260308,174260414⟩]
theorem checked69794 : checkPrefixCuts (2^48) 9151971329 10 Manual.Count131072.C069794.packed 64 cuts69794 = true := by
 decide +kernel
def cuts69795 : List PrefixCut := [⟨58,158388338,158388435⟩,
⟨64,174719136,174719241⟩]
theorem checked69795 : checkPrefixCuts (2^48) 9152102401 10 Manual.Count131072.C069795.packed 64 cuts69795 = true := by
 decide +kernel
def pointBounds69795 : List (Nat × Nat × Nat) := [(9152221184,115777928115912,115778317600029)]
theorem point_links_checked69795 : (cuts69795.take 1).map (fun c => (9152102401-1+2*2^10*c.k,115777769727574+c.lower,115778159211594+c.upper)) = pointBounds69795 := by
 decide +kernel
def cuts69796 : List PrefixCut := [⟨64,174624381,174624484⟩]
theorem checked69796 : checkPrefixCuts (2^48) 9152233473 10 Manual.Count131072.C069796.packed 64 cuts69796 = true := by
 decide +kernel
def cuts69797 : List PrefixCut := [⟨64,175790517,175790619⟩]
theorem checked69797 : checkPrefixCuts (2^48) 9152364545 10 Manual.Count131072.C069797.packed 64 cuts69797 = true := by
 decide +kernel
def cuts69798 : List PrefixCut := [⟨6,16330308,16330317⟩,
⟨64,176925891,176925994⟩]
theorem checked69798 : checkPrefixCuts (2^48) 9152495617 10 Manual.Count131072.C069798.packed 64 cuts69798 = true := by
 decide +kernel
def pointBounds69798 : List (Nat × Nat × Nat) := [(9152507904,115778311191916,115778700676255)]
theorem point_links_checked69798 : (cuts69798.take 1).map (fun c => (9152495617-1+2*2^10*c.k,115778294861608+c.lower,115778684345938+c.upper)) = pointBounds69798 := by
 decide +kernel
def cuts69799 : List PrefixCut := [⟨64,176769579,176769688⟩]
theorem checked69799 : checkPrefixCuts (2^48) 9152626689 10 Manual.Count131072.C069799.packed 64 cuts69799 = true := by
 decide +kernel
def cuts69800 : List PrefixCut := [⟨18,49296985,49297013⟩,
⟨64,175137159,175137263⟩]
theorem checked69800 : checkPrefixCuts (2^48) 9152757761 10 Manual.Count131072.C069800.packed 64 cuts69800 = true := by
 decide +kernel
def pointBounds69800 : List (Nat × Nat × Nat) := [(9152794624,115778697854063,115779087338633)]
theorem point_links_checked69800 : (cuts69800.take 1).map (fun c => (9152757761-1+2*2^10*c.k,115778648557078+c.lower,115779038041620+c.upper)) = pointBounds69800 := by
 decide +kernel
def cuts69801 : List PrefixCut := [⟨64,176426256,176426359⟩]
theorem checked69801 : checkPrefixCuts (2^48) 9152888833 10 Manual.Count131072.C069801.packed 64 cuts69801 = true := by
 decide +kernel
def cuts69802 : List PrefixCut := [⟨30,84721840,84721890⟩,
⟨64,178268844,178268949⟩]
theorem checked69802 : checkPrefixCuts (2^48) 9153019905 10 Manual.Count131072.C069802.packed 64 cuts69802 = true := by
 decide +kernel
def pointBounds69802 : List (Nat × Nat × Nat) := [(9153081344,115779084842333,115779474327132)]
theorem point_links_checked69802 : (cuts69802.take 1).map (fun c => (9153019905-1+2*2^10*c.k,115779000120493+c.lower,115779389605242+c.upper)) = pointBounds69802 := by
 decide +kernel
def cuts69803 : List PrefixCut := [⟨64,176175200,176175303⟩]
theorem checked69803 : checkPrefixCuts (2^48) 9153150977 10 Manual.Count131072.C069803.packed 64 cuts69803 = true := by
 decide +kernel
def cuts69804 : List PrefixCut := [⟨42,113625346,113625413⟩,
⟨64,173743333,173743433⟩]
theorem checked69804 : checkPrefixCuts (2^48) 9153282049 10 Manual.Count131072.C069804.packed 64 cuts69804 = true := by
 decide +kernel
def pointBounds69804 : List (Nat × Nat × Nat) := [(9153368064,115779468189883,115779857674907)]
theorem point_links_checked69804 : (cuts69804.take 1).map (fun c => (9153282049-1+2*2^10*c.k,115779354564537+c.lower,115779744049494+c.upper)) = pointBounds69804 := by
 decide +kernel
def cuts69805 : List PrefixCut := [⟨64,172941331,172941436⟩]
theorem checked69805 : checkPrefixCuts (2^48) 9153413121 10 Manual.Count131072.C069805.packed 64 cuts69805 = true := by
 decide +kernel
def cuts69806 : List PrefixCut := [⟨54,147293395,147293483⟩,
⟨64,174968365,174968469⟩]
theorem checked69806 : checkPrefixCuts (2^48) 9153544193 10 Manual.Count131072.C069806.packed 64 cuts69806 = true := by
 decide +kernel
def pointBounds69806 : List (Nat × Nat × Nat) := [(9153654784,115779848542596,115780238027846)]
theorem point_links_checked69806 : (cuts69806.take 1).map (fun c => (9153544193-1+2*2^10*c.k,115779701249201+c.lower,115780090734363+c.upper)) = pointBounds69806 := by
 decide +kernel
def cuts69807 : List PrefixCut := [⟨64,175150365,175150469⟩]
theorem checked69807 : checkPrefixCuts (2^48) 9153675265 10 Manual.Count131072.C069807.packed 64 cuts69807 = true := by
 decide +kernel
def cuts69808 : List PrefixCut := [⟨64,177331062,177331167⟩]
theorem checked69808 : checkPrefixCuts (2^48) 9153806337 10 Manual.Count131072.C069808.packed 64 cuts69808 = true := by
 decide +kernel
def cuts69809 : List PrefixCut := [⟨2,4704604,4704607⟩,
⟨64,175053090,175053192⟩]
theorem checked69809 : checkPrefixCuts (2^48) 9153937409 10 Manual.Count131072.C069809.packed 64 cuts69809 = true := by
 decide +kernel
def pointBounds69809 : List (Nat × Nat × Nat) := [(9153941504,115780233403597,115780622889075)]
theorem point_links_checked69809 : (cuts69809.take 1).map (fun c => (9153937409-1+2*2^10*c.k,115780228698993+c.lower,115780618184468+c.upper)) = pointBounds69809 := by
 decide +kernel
def cuts69810 : List PrefixCut := [⟨64,174804603,174804716⟩]
theorem checked69810 : checkPrefixCuts (2^48) 9154068481 10 Manual.Count131072.C069810.packed 64 cuts69810 = true := by
 decide +kernel
def cuts69811 : List PrefixCut := [⟨14,39173110,39173129⟩,
⟨64,175632311,175632412⟩]
theorem checked69811 : checkPrefixCuts (2^48) 9154199553 10 Manual.Count131072.C069811.packed 64 cuts69811 = true := by
 decide +kernel
def pointBounds69811 : List (Nat × Nat × Nat) := [(9154228224,115780617729796,115781007215505)]
theorem point_links_checked69811 : (cuts69811.take 1).map (fun c => (9154199553-1+2*2^10*c.k,115780578556686+c.lower,115780968042376+c.upper)) = pointBounds69811 := by
 decide +kernel
def cuts69812 : List PrefixCut := [⟨64,173877188,173877296⟩]
theorem checked69812 : checkPrefixCuts (2^48) 9154330625 10 Manual.Count131072.C069812.packed 64 cuts69812 = true := by
 decide +kernel
def cuts69813 : List PrefixCut := [⟨26,72409658,72409702⟩,
⟨64,176641920,176642026⟩]
theorem checked69813 : checkPrefixCuts (2^48) 9154461697 10 Manual.Count131072.C069813.packed 64 cuts69813 = true := by
 decide +kernel
def pointBounds69813 : List (Nat × Nat × Nat) := [(9154514944,115781000475843,115781389961786)]
theorem point_links_checked69813 : (cuts69813.take 1).map (fun c => (9154461697-1+2*2^10*c.k,115780928066185+c.lower,115781317552084+c.upper)) = pointBounds69813 := by
 decide +kernel
def cuts69814 : List PrefixCut := [⟨64,174948318,174948416⟩]
theorem checked69814 : checkPrefixCuts (2^48) 9154592769 10 Manual.Count131072.C069814.packed 64 cuts69814 = true := by
 decide +kernel
def cuts69815 : List PrefixCut := [⟨38,104875555,104875620⟩,
⟨64,175683734,175683838⟩]
theorem checked69815 : checkPrefixCuts (2^48) 9154723841 10 Manual.Count131072.C069815.packed 64 cuts69815 = true := by
 decide +kernel
def pointBounds69815 : List (Nat × Nat × Nat) := [(9154801664,115781384531978,115781774018146)]
theorem point_links_checked69815 : (cuts69815.take 1).map (fun c => (9154723841-1+2*2^10*c.k,115781279656423+c.lower,115781669142526+c.upper)) = pointBounds69815 := by
 decide +kernel
def cuts69816 : List PrefixCut := [⟨64,175896437,175896538⟩]
theorem checked69816 : checkPrefixCuts (2^48) 9154854913 10 Manual.Count131072.C069816.packed 64 cuts69816 = true := by
 decide +kernel
def cuts69817 : List PrefixCut := [⟨50,136355661,136355742⟩,
⟨64,175125280,175125382⟩]
theorem checked69817 : checkPrefixCuts (2^48) 9154985985 10 Manual.Count131072.C069817.packed 64 cuts69817 = true := by
 decide +kernel
def pointBounds69817 : List (Nat × Nat × Nat) := [(9155088384,115781767592255,115782157078644)]
theorem point_links_checked69817 : (cuts69817.take 1).map (fun c => (9154985985-1+2*2^10*c.k,115781631236594+c.lower,115782020722902+c.upper)) = pointBounds69817 := by
 decide +kernel
def cuts69818 : List PrefixCut := [⟨64,175676175,175676285⟩]
theorem checked69818 : checkPrefixCuts (2^48) 9155117057 10 Manual.Count131072.C069818.packed 64 cuts69818 = true := by
 decide +kernel
def cuts69819 : List PrefixCut := [⟨62,167926109,167926208⟩,
⟨64,173828998,173829101⟩]
theorem checked69819 : checkPrefixCuts (2^48) 9155248129 10 Manual.Count131072.C069819.packed 64 cuts69819 = true := by
 decide +kernel
def pointBounds69819 : List (Nat × Nat × Nat) := [(9155375104,115782149964158,115782539450777)]
theorem point_links_checked69819 : (cuts69819.take 1).map (fun c => (9155248129-1+2*2^10*c.k,115781982038049+c.lower,115782371524569+c.upper)) = pointBounds69819 := by
 decide +kernel
def cuts69820 : List PrefixCut := [⟨64,174226183,174226287⟩]
theorem checked69820 : checkPrefixCuts (2^48) 9155379201 10 Manual.Count131072.C069820.packed 64 cuts69820 = true := by
 decide +kernel
def cuts69821 : List PrefixCut := [⟨64,174438902,174439008⟩]
theorem checked69821 : checkPrefixCuts (2^48) 9155510273 10 Manual.Count131072.C069821.packed 64 cuts69821 = true := by
 decide +kernel
def cuts69822 : List PrefixCut := [⟨10,27177071,27177089⟩,
⟨64,175358687,175358795⟩]
theorem checked69822 : checkPrefixCuts (2^48) 9155641345 10 Manual.Count131072.C069822.packed 64 cuts69822 = true := by
 decide +kernel
def pointBounds69822 : List (Nat × Nat × Nat) := [(9155661824,115782531709203,115782921196054)]
theorem point_links_checked69822 : (cuts69822.take 1).map (fun c => (9155641345-1+2*2^10*c.k,115782504532132+c.lower,115782894018965+c.upper)) = pointBounds69822 := by
 decide +kernel
def cuts69823 : List PrefixCut := [⟨64,176954787,176954893⟩]
theorem checked69823 : checkPrefixCuts (2^48) 9155772417 10 Manual.Count131072.C069823.packed 64 cuts69823 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000306
