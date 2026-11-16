import PlattAssemblyKernel
import PlattCertificates.Count131072.C017808
import PlattCertificates.Count131072.C017809
import PlattCertificates.Count131072.C017810
import PlattCertificates.Count131072.C017811
import PlattCertificates.Count131072.C017812
import PlattCertificates.Count131072.C017813
import PlattCertificates.Count131072.C017814
import PlattCertificates.Count131072.C017815
import PlattCertificates.Count131072.C017816
import PlattCertificates.Count131072.C017817
import PlattCertificates.Count131072.C017818
import PlattCertificates.Count131072.C017819
import PlattCertificates.Count131072.C017820
import PlattCertificates.Count131072.C017821
import PlattCertificates.Count131072.C017822
import PlattCertificates.Count131072.C017823
import PlattCertificates.Count131072.C017824
import PlattCertificates.Count131072.C017825
import PlattCertificates.Count131072.C017826
import PlattCertificates.Count131072.C017827
import PlattCertificates.Count131072.C017828
import PlattCertificates.Count131072.C017829
import PlattCertificates.Count131072.C017830
import PlattCertificates.Count131072.C017831
import PlattCertificates.Count131072.C017832
import PlattCertificates.Count131072.C017833
import PlattCertificates.Count131072.C017834
import PlattCertificates.Count131072.C017835
import PlattCertificates.Count131072.C017836
import PlattCertificates.Count131072.C017837
import PlattCertificates.Count131072.C017838
import PlattCertificates.Count131072.C017839
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000244
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts17808 : List PrefixCut := [⟨4,23355272,23355287⟩,
⟨76,424722170,424722431⟩,
⟨128,721345198,721345643⟩]
theorem checked17808 : checkPrefixCuts (2^48) 2338062337 9 Manual.Count131072.C017808.packed 128 cuts17808 = true := by
 decide +kernel
def pointBounds17808 : List (Nat × Nat × Nat) := [(2338066432,98512663200893,98513042665985),(2338140160,98513064567791,98513444033129)]
theorem point_links_checked17808 : (cuts17808.take 2).map (fun c => (2338062337-1+2*2^9*c.k,98512639845621+c.lower,98513019310698+c.upper)) = pointBounds17808 := by
 decide +kernel
def cuts17809 : List PrefixCut := [⟨20,114482165,114482235⟩,
⟨92,518351641,518351959⟩,
⟨128,730814504,730814947⟩]
theorem checked17809 : checkPrefixCuts (2^48) 2338193409 9 Manual.Count131072.C017809.packed 128 cuts17809 = true := by
 decide +kernel
def pointBounds17809 : List (Nat × Nat × Nat) := [(2338213888,98513475672984,98513855138576),(2338287616,98513879542460,98514259008300)]
theorem point_links_checked17809 : (cuts17809.take 2).map (fun c => (2338193409-1+2*2^9*c.k,98513361190819+c.lower,98513740656341+c.upper)) = pointBounds17809 := by
 decide +kernel
def cuts17810 : List PrefixCut := [⟨36,212339126,212339256⟩,
⟨108,626896105,626896485⟩,
⟨128,742690494,742690944⟩]
theorem checked17810 : checkPrefixCuts (2^48) 2338324481 9 Manual.Count131072.C017810.packed 128 cuts17810 = true := by
 decide +kernel
def pointBounds17810 : List (Nat × Nat × Nat) := [(2338361344,98514304344449,98514683810544),(2338435072,98514718901428,98515098367773)]
theorem point_links_checked17810 : (cuts17810.take 2).map (fun c => (2338324481-1+2*2^9*c.k,98514092005323+c.lower,98514471471288+c.upper)) = pointBounds17810 := by
 decide +kernel
def cuts17811 : List PrefixCut := [⟨52,292249812,292249992⟩,
⟨124,708104796,708105231⟩,
⟨128,729168009,729168458⟩]
theorem checked17811 : checkPrefixCuts (2^48) 2338455553 9 Manual.Count131072.C017811.packed 128 cuts17811 = true := by
 decide +kernel
def pointBounds17811 : List (Nat × Nat × Nat) := [(2338508800,98515126945629,98515506412224),(2338582528,98515542800613,98515922267463)]
theorem point_links_checked17811 : (cuts17811.take 2).map (fun c => (2338455553-1+2*2^9*c.k,98514834695817+c.lower,98515214162232+c.upper)) = pointBounds17811 := by
 decide +kernel
def cuts17812 : List PrefixCut := [⟨68,388519910,388520145⟩,
⟨128,738755784,738756237⟩]
theorem checked17812 : checkPrefixCuts (2^48) 2338586625 9 Manual.Count131072.C017812.packed 128 cuts17812 = true := by
 decide +kernel
def pointBounds17812 : List (Nat × Nat × Nat) := [(2338656256,98515952383736,98516331850835)]
theorem point_links_checked17812 : (cuts17812.take 1).map (fun c => (2338586625-1+2*2^9*c.k,98515563863826+c.lower,98515943330690+c.upper)) = pointBounds17812 := by
 decide +kernel
def cuts17813 : List PrefixCut := [⟨12,69805348,69805391⟩,
⟨84,479362665,479362962⟩,
⟨128,730049192,730049642⟩]
theorem checked17813 : checkPrefixCuts (2^48) 2338717697 9 Manual.Count131072.C017813.packed 128 cuts17813 = true := by
 decide +kernel
def pointBounds17813 : List (Nat × Nat × Nat) := [(2338729984,98516372424958,98516751892318),(2338803712,98516781982275,98517161449889)]
theorem point_links_checked17813 : (cuts17813.take 2).map (fun c => (2338717697-1+2*2^9*c.k,98516302619610+c.lower,98516682086927+c.upper)) = pointBounds17813 := by
 decide +kernel
def cuts17814 : List PrefixCut := [⟨28,158617185,158617280⟩,
⟨100,566945252,566945599⟩,
⟨128,727360628,727361074⟩]
theorem checked17814 : checkPrefixCuts (2^48) 2338848769 9 Manual.Count131072.C017814.packed 128 cuts17814 = true := by
 decide +kernel
def pointBounds17814 : List (Nat × Nat × Nat) := [(2338877440,98517191285987,98517570753849),(2338951168,98517599614054,98517979082168)]
theorem point_links_checked17814 : (cuts17814.take 2).map (fun c => (2338848769-1+2*2^9*c.k,98517032668802+c.lower,98517412136569+c.upper)) = pointBounds17814 := by
 decide +kernel
def cuts17815 : List PrefixCut := [⟨44,254759172,254759327⟩,
⟨116,667513988,667514396⟩,
⟨128,733457270,733457721⟩]
theorem checked17815 : checkPrefixCuts (2^48) 2338979841 9 Manual.Count131072.C017815.packed 128 cuts17815 = true := by
 decide +kernel
def pointBounds17815 : List (Nat × Nat × Nat) := [(2339024896,98518014788602,98518394256970),(2339098624,98518427543418,98518807012039)]
theorem point_links_checked17815 : (cuts17815.take 2).map (fun c => (2338979841-1+2*2^9*c.k,98517760029430+c.lower,98518139497643+c.upper)) = pointBounds17815 := by
 decide +kernel
def cuts17816 : List PrefixCut := [⟨60,344391802,344392009⟩,
⟨128,730648483,730648924⟩]
theorem checked17816 : checkPrefixCuts (2^48) 2339110913 9 Manual.Count131072.C017816.packed 128 cuts17816 = true := by
 decide +kernel
def pointBounds17816 : List (Nat × Nat × Nat) := [(2339172352,98518837878502,98519217347373)]
theorem point_links_checked17816 : (cuts17816.take 1).map (fun c => (2339110913-1+2*2^9*c.k,98518493486700+c.lower,98518872955364+c.upper)) = pointBounds17816 := by
 decide +kernel
def cuts17817 : List PrefixCut := [⟨4,22862185,22862199⟩,
⟨76,440030044,440030310⟩,
⟨128,735420617,735421063⟩]
theorem checked17817 : checkPrefixCuts (2^48) 2339241985 9 Manual.Count131072.C017817.packed 128 cuts17817 = true := by
 decide +kernel
def pointBounds17817 : List (Nat × Nat × Nat) := [(2339246080,98519246997368,98519626466487),(2339319808,98519664165227,98520043634598)]
theorem point_links_checked17817 : (cuts17817.take 2).map (fun c => (2339241985-1+2*2^9*c.k,98519224135183+c.lower,98519603604288+c.upper)) = pointBounds17817 := by
 decide +kernel
def cuts17818 : List PrefixCut := [⟨20,115988608,115988683⟩,
⟨92,530603412,530603735⟩,
⟨128,738026207,738026657⟩]
theorem checked17818 : checkPrefixCuts (2^48) 2339373057 9 Manual.Count131072.C017818.packed 128 cuts17818 = true := by
 decide +kernel
def pointBounds17818 : List (Nat × Nat × Nat) := [(2339393536,98520075544408,98520455014034),(2339467264,98520490159212,98520869629086)]
theorem point_links_checked17818 : (cuts17818.take 2).map (fun c => (2339373057-1+2*2^9*c.k,98519959555800+c.lower,98520339025351+c.upper)) = pointBounds17818 := by
 decide +kernel
def cuts17819 : List PrefixCut := [⟨36,204050771,204050901⟩,
⟨108,620564294,620564676⟩,
⟨128,735458141,735458595⟩]
theorem checked17819 : checkPrefixCuts (2^48) 2339504129 9 Manual.Count131072.C017819.packed 128 cuts17819 = true := by
 decide +kernel
def pointBounds17819 : List (Nat × Nat × Nat) := [(2339540992,98520901632778,98521281102909),(2339614720,98521318146301,98521697616684)]
theorem point_links_checked17819 : (cuts17819.take 2).map (fun c => (2339504129-1+2*2^9*c.k,98520697582007+c.lower,98521077052008+c.upper)) = pointBounds17819 := by
 decide +kernel
def cuts17820 : List PrefixCut := [⟨52,290297900,290298080⟩,
⟨124,700529444,700529880⟩,
⟨128,724950452,724950902⟩]
theorem checked17820 : checkPrefixCuts (2^48) 2339635201 9 Manual.Count131072.C017820.packed 128 cuts17820 = true := by
 decide +kernel
def pointBounds17820 : List (Nat × Nat × Nat) := [(2339688448,98521723338048,98522102808683),(2339762176,98522133569592,98522513040483)]
theorem point_links_checked17820 : (cuts17820.take 2).map (fun c => (2339635201-1+2*2^9*c.k,98521433040148+c.lower,98521812510603+c.upper)) = pointBounds17820 := by
 decide +kernel
def cuts17821 : List PrefixCut := [⟨68,382068435,382068670⟩,
⟨128,720218425,720218869⟩]
theorem checked17821 : checkPrefixCuts (2^48) 2339766273 9 Manual.Count131072.C017821.packed 128 cuts17821 = true := by
 decide +kernel
def pointBounds17821 : List (Nat × Nat × Nat) := [(2339835904,98522540059035,98522919530175)]
theorem point_links_checked17821 : (cuts17821.take 1).map (fun c => (2339766273-1+2*2^9*c.k,98522157990600+c.lower,98522537461505+c.upper)) = pointBounds17821 := by
 decide +kernel
def cuts17822 : List PrefixCut := [⟨12,68567225,68567265⟩,
⟨84,481045596,481045884⟩,
⟨128,731365160,731365597⟩]
theorem checked17822 : checkPrefixCuts (2^48) 2339897345 9 Manual.Count131072.C017822.packed 128 cuts17822 = true := by
 decide +kernel
def pointBounds17822 : List (Nat × Nat × Nat) := [(2339909632,98522946776250,98523326247639),(2339983360,98523359254621,98523738726258)]
theorem point_links_checked17822 : (cuts17822.take 2).map (fun c => (2339897345-1+2*2^9*c.k,98522878209025+c.lower,98523257680374+c.upper)) = pointBounds17822 := by
 decide +kernel
def cuts17823 : List PrefixCut := [⟨28,159018381,159018477⟩,
⟨100,565817469,565817815⟩,
⟨128,716770054,716770495⟩]
theorem checked17823 : checkPrefixCuts (2^48) 2340028417 9 Manual.Count131072.C017823.packed 128 cuts17823 = true := by
 decide +kernel
def pointBounds17823 : List (Nat × Nat × Nat) := [(2340057088,98523768592566,98524148064448),(2340130816,98524175391654,98524554863786)]
theorem point_links_checked17823 : (cuts17823.take 2).map (fun c => (2340028417-1+2*2^9*c.k,98523609574185+c.lower,98523989045971+c.upper)) = pointBounds17823 := by
 decide +kernel
def cuts17824 : List PrefixCut := [⟨44,255472714,255472873⟩,
⟨116,664531449,664531860⟩,
⟨128,734410524,734410978⟩]
theorem checked17824 : checkPrefixCuts (2^48) 2340159489 9 Manual.Count131072.C017824.packed 128 cuts17824 = true := by
 decide +kernel
def pointBounds17824 : List (Nat × Nat × Nat) := [(2340204544,98524581816953,98524961289339),(2340278272,98524990875688,98525370348326)]
theorem point_links_checked17824 : (cuts17824.take 2).map (fun c => (2340159489-1+2*2^9*c.k,98524326344239+c.lower,98524705816466+c.upper)) = pointBounds17824 := by
 decide +kernel
def cuts17825 : List PrefixCut := [⟨60,337723545,337723757⟩,
⟨128,728235503,728235956⟩]
theorem checked17825 : checkPrefixCuts (2^48) 2340290561 9 Manual.Count131072.C017825.packed 128 cuts17825 = true := by
 decide +kernel
def pointBounds17825 : List (Nat × Nat × Nat) := [(2340352000,98525398478308,98525777951201)]
theorem point_links_checked17825 : (cuts17825.take 1).map (fun c => (2340290561-1+2*2^9*c.k,98525060754763+c.lower,98525440227444+c.upper)) = pointBounds17825 := by
 decide +kernel
def cuts17826 : List PrefixCut := [⟨4,21768261,21768275⟩,
⟨76,422971080,422971338⟩,
⟨128,719295117,719295556⟩]
theorem checked17826 : checkPrefixCuts (2^48) 2340421633 9 Manual.Count131072.C017826.packed 128 cuts17826 = true := by
 decide +kernel
def pointBounds17826 : List (Nat × Nat × Nat) := [(2340425728,98525810758527,98526190231675),(2340499456,98526211961346,98526591434738)]
theorem point_links_checked17826 : (cuts17826.take 2).map (fun c => (2340421633-1+2*2^9*c.k,98525788990266+c.lower,98526168463400+c.upper)) = pointBounds17826 := by
 decide +kernel
def cuts17827 : List PrefixCut := [⟨20,112322369,112322440⟩,
⟨92,527930699,527931023⟩,
⟨128,732002107,732002557⟩]
theorem checked17827 : checkPrefixCuts (2^48) 2340552705 9 Manual.Count131072.C017827.packed 128 cuts17827 = true := by
 decide +kernel
def pointBounds17827 : List (Nat × Nat × Nat) := [(2340573184,98526620607752,98527000081396),(2340646912,98527036216082,98527415689979)]
theorem point_links_checked17827 : (cuts17827.take 2).map (fun c => (2340552705-1+2*2^9*c.k,98526508285383+c.lower,98526887758956+c.upper)) = pointBounds17827 := by
 decide +kernel
def cuts17828 : List PrefixCut := [⟨36,203466969,203467095⟩,
⟨108,620852871,620853255⟩,
⟨128,731720655,731721107⟩]
theorem checked17828 : checkPrefixCuts (2^48) 2340683777 9 Manual.Count131072.C017828.packed 128 cuts17828 = true := by
 decide +kernel
def pointBounds17828 : List (Nat × Nat × Nat) := [(2340720640,98527443754459,98527823228608),(2340794368,98527861140361,98528240614768)]
theorem point_links_checked17828 : (cuts17828.take 2).map (fun c => (2340683777-1+2*2^9*c.k,98527240287490+c.lower,98527619761513+c.upper)) = pointBounds17828 := by
 decide +kernel
def cuts17829 : List PrefixCut := [⟨52,301935640,301935823⟩,
⟨124,719295343,719295782⟩,
⟨128,742261167,742261619⟩]
theorem checked17829 : checkPrefixCuts (2^48) 2340814849 9 Manual.Count131072.C017829.packed 128 cuts17829 = true := by
 decide +kernel
def pointBounds17829 : List (Nat × Nat × Nat) := [(2340868096,98528273943785,98528653418443),(2340941824,98528691303488,98529070778402)]
theorem point_links_checked17829 : (cuts17829.take 2).map (fun c => (2340814849-1+2*2^9*c.k,98527972008145+c.lower,98528351482620+c.upper)) = pointBounds17829 := by
 decide +kernel
def cuts17830 : List PrefixCut := [⟨68,388008077,388008315⟩,
⟨128,726949594,726950040⟩]
theorem checked17830 : checkPrefixCuts (2^48) 2340945921 9 Manual.Count131072.C017830.packed 128 cuts17830 = true := by
 decide +kernel
def pointBounds17830 : List (Nat × Nat × Nat) := [(2341015552,98529102277389,98529481752554)]
theorem point_links_checked17830 : (cuts17830.take 1).map (fun c => (2340945921-1+2*2^9*c.k,98528714269312+c.lower,98529093744239+c.upper)) = pointBounds17830 := by
 decide +kernel
def cuts17831 : List PrefixCut := [⟨12,69374304,69374346⟩,
⟨84,486454164,486454457⟩,
⟨128,737970089,737970535⟩]
theorem checked17831 : checkPrefixCuts (2^48) 2341076993 9 Manual.Count131072.C017831.packed 128 cuts17831 = true := by
 decide +kernel
def pointBounds17831 : List (Nat × Nat × Nat) := [(2341089280,98529510593210,98529890068625),(2341163008,98529927673070,98530307148736)]
theorem point_links_checked17831 : (cuts17831.take 2).map (fun c => (2341076993-1+2*2^9*c.k,98529441218906+c.lower,98529820694279+c.upper)) = pointBounds17831 := by
 decide +kernel
def cuts17832 : List PrefixCut := [⟨28,160380944,160381044⟩,
⟨100,574188479,574188830⟩,
⟨128,731797368,731797815⟩]
theorem checked17832 : checkPrefixCuts (2^48) 2341208065 9 Manual.Count131072.C017832.packed 128 cuts17832 = true := by
 decide +kernel
def pointBounds17832 : List (Nat × Nat × Nat) := [(2341236736,98530339569939,98530719045858),(2341310464,98530753377474,98531132853644)]
theorem point_links_checked17832 : (cuts17832.take 2).map (fun c => (2341208065-1+2*2^9*c.k,98530179188995+c.lower,98530558664814+c.upper)) = pointBounds17832 := by
 decide +kernel
def cuts17833 : List PrefixCut := [⟨44,254502464,254502621⟩,
⟨116,665879568,665879977⟩,
⟨128,734641516,734641966⟩]
theorem checked17833 : checkPrefixCuts (2^48) 2341339137 9 Manual.Count131072.C017833.packed 128 cuts17833 = true := by
 decide +kernel
def pointBounds17833 : List (Nat × Nat × Nat) := [(2341384192,98531165488827,98531544965250),(2341457920,98531576865931,98531956342606)]
theorem point_links_checked17833 : (cuts17833.take 2).map (fun c => (2341339137-1+2*2^9*c.k,98530910986363+c.lower,98531290462629+c.upper)) = pointBounds17833 := by
 decide +kernel
def cuts17834 : List PrefixCut := [⟨60,341640532,341640738⟩,
⟨128,739528775,739529218⟩]
theorem checked17834 : checkPrefixCuts (2^48) 2341470209 9 Manual.Count131072.C017834.packed 128 cuts17834 = true := by
 decide +kernel
def pointBounds17834 : List (Nat × Nat × Nat) := [(2341531648,98531987268411,98532366745333)]
theorem point_links_checked17834 : (cuts17834.take 1).map (fun c => (2341470209-1+2*2^9*c.k,98531645627879+c.lower,98532025104595+c.upper)) = pointBounds17834 := by
 decide +kernel
def cuts17835 : List PrefixCut := [⟨4,22959356,22959368⟩,
⟨76,430090493,430090754⟩,
⟨128,724943075,724943518⟩]
theorem checked17835 : checkPrefixCuts (2^48) 2341601281 9 Manual.Count131072.C017835.packed 128 cuts17835 = true := by
 decide +kernel
def pointBounds17835 : List (Nat × Nat × Nat) := [(2341605376,98532408116010,98532787593181),(2341679104,98532815247147,98533194724567)]
theorem point_links_checked17835 : (cuts17835.take 2).map (fun c => (2341601281-1+2*2^9*c.k,98532385156654+c.lower,98532764633813+c.upper)) = pointBounds17835 := by
 decide +kernel
def cuts17836 : List PrefixCut := [⟨20,113948566,113948637⟩,
⟨92,525501368,525501684⟩,
⟨128,733917173,733917619⟩]
theorem checked17836 : checkPrefixCuts (2^48) 2341732353 9 Manual.Count131072.C017836.packed 128 cuts17836 = true := by
 decide +kernel
def pointBounds17836 : List (Nat × Nat × Nat) := [(2341752832,98533224048295,98533603525968),(2341826560,98533635601097,98534015079015)]
theorem point_links_checked17836 : (cuts17836.take 2).map (fun c => (2341732353-1+2*2^9*c.k,98533110099729+c.lower,98533489577331+c.upper)) = pointBounds17836 := by
 decide +kernel
def cuts17837 : List PrefixCut := [⟨36,205768304,205768432⟩,
⟨108,604555112,604555486⟩,
⟨128,714645944,714646386⟩]
theorem checked17837 : checkPrefixCuts (2^48) 2341863425 9 Manual.Count131072.C017837.packed 128 cuts17837 = true := by
 decide +kernel
def pointBounds17837 : List (Nat × Nat × Nat) := [(2341900288,98534049785206,98534429263382),(2341974016,98534448572014,98534828050436)]
theorem point_links_checked17837 : (cuts17837.take 2).map (fun c => (2341863425-1+2*2^9*c.k,98533844016902+c.lower,98534223494950+c.upper)) = pointBounds17837 := by
 decide +kernel
def cuts17838 : List PrefixCut := [⟨52,296615617,296615802⟩,
⟨124,699944297,699944730⟩,
⟨128,723018731,723019180⟩]
theorem checked17838 : checkPrefixCuts (2^48) 2341994497 9 Manual.Count131072.C017838.packed 128 cuts17838 = true := by
 decide +kernel
def pointBounds17838 : List (Nat × Nat × Nat) := [(2342047744,98534855278463,98535234757138),(2342121472,98535258607143,98535638086066)]
theorem point_links_checked17838 : (cuts17838.take 2).map (fun c => (2341994497-1+2*2^9*c.k,98534558662846+c.lower,98534938141336+c.upper)) = pointBounds17838 := by
 decide +kernel
def cuts17839 : List PrefixCut := [⟨68,389254784,389255029⟩,
⟨128,732471973,732472434⟩]
theorem checked17839 : checkPrefixCuts (2^48) 2342125569 9 Manual.Count131072.C017839.packed 128 cuts17839 = true := by
 decide +kernel
def pointBounds17839 : List (Nat × Nat × Nat) := [(2342195200,98535670936361,98536050415545)]
theorem point_links_checked17839 : (cuts17839.take 1).map (fun c => (2342125569-1+2*2^9*c.k,98535281681577+c.lower,98535661160516+c.upper)) = pointBounds17839 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000244
