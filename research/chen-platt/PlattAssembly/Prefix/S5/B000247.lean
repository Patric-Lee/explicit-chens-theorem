import PlattAssemblyKernel
import PlattCertificates.Count131072.C047904
import PlattCertificates.Count131072.C047905
import PlattCertificates.Count131072.C047906
import PlattCertificates.Count131072.C047907
import PlattCertificates.Count131072.C047908
import PlattCertificates.Count131072.C047909
import PlattCertificates.Count131072.C047910
import PlattCertificates.Count131072.C047911
import PlattCertificates.Count131072.C047912
import PlattCertificates.Count131072.C047913
import PlattCertificates.Count131072.C047914
import PlattCertificates.Count131072.C047915
import PlattCertificates.Count131072.C047916
import PlattCertificates.Count131072.C047917
import PlattCertificates.Count131072.C047918
import PlattCertificates.Count131072.C047919
import PlattCertificates.Count131072.C047920
import PlattCertificates.Count131072.C047921
import PlattCertificates.Count131072.C047922
import PlattCertificates.Count131072.C047923
import PlattCertificates.Count131072.C047924
import PlattCertificates.Count131072.C047925
import PlattCertificates.Count131072.C047926
import PlattCertificates.Count131072.C047927
import PlattCertificates.Count131072.C047928
import PlattCertificates.Count131072.C047929
import PlattCertificates.Count131072.C047930
import PlattCertificates.Count131072.C047931
import PlattCertificates.Count131072.C047932
import PlattCertificates.Count131072.C047933
import PlattCertificates.Count131072.C047934
import PlattCertificates.Count131072.C047935
namespace ChenEffective.PlattWindow.Assembly.Prefix.S5.B000247
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts47904 : List PrefixCut := [⟨64,260827738,260827889⟩]
theorem checked47904 : checkPrefixCuts (2^48) 6282805249 10 Manual.Count131072.C047904.packed 64 cuts47904 = true := by
 decide +kernel
def cuts47905 : List PrefixCut := [⟨16,66617272,66617310⟩,
⟨64,262614268,262614417⟩]
theorem checked47905 : checkPrefixCuts (2^48) 6282936321 10 Manual.Count131072.C047905.packed 64 cuts47905 = true := by
 decide +kernel
def pointBounds47905 : List (Nat × Nat × Nat) := [(6282969088,111123783623938,111124170441689)]
theorem point_links_checked47905 : (cuts47905.take 1).map (fun c => (6282936321-1+2*2^10*c.k,111123717006666+c.lower,111124103824379+c.upper)) = pointBounds47905 := by
 decide +kernel
def cuts47906 : List PrefixCut := [⟨48,196486704,196486819⟩,
⟨64,261623206,261623360⟩]
theorem checked47906 : checkPrefixCuts (2^48) 6283067393 10 Manual.Count131072.C047906.packed 64 cuts47906 = true := by
 decide +kernel
def pointBounds47906 : List (Nat × Nat × Nat) := [(6283165696,111124176107638,111124562925615)]
theorem point_links_checked47906 : (cuts47906.take 1).map (fun c => (6283067393-1+2*2^10*c.k,111123979620934+c.lower,111124366438796+c.upper)) = pointBounds47906 := by
 decide +kernel
def cuts47907 : List PrefixCut := [⟨64,260676997,260677144⟩]
theorem checked47907 : checkPrefixCuts (2^48) 6283198465 10 Manual.Count131072.C047907.packed 64 cuts47907 = true := by
 decide +kernel
def cuts47908 : List PrefixCut := [⟨16,62984547,62984586⟩,
⟨64,259462035,259462192⟩]
theorem checked47908 : checkPrefixCuts (2^48) 6283329537 10 Manual.Count131072.C047908.packed 64 cuts47908 = true := by
 decide +kernel
def pointBounds47908 : List (Nat × Nat × Nat) := [(6283362304,111124564905684,111124951723886)]
theorem point_links_checked47908 : (cuts47908.take 1).map (fun c => (6283329537-1+2*2^10*c.k,111124501921137+c.lower,111124888739300+c.upper)) = pointBounds47908 := by
 decide +kernel
def cuts47909 : List PrefixCut := [⟨48,194100240,194100351⟩,
⟨64,258919099,258919245⟩]
theorem checked47909 : checkPrefixCuts (2^48) 6283460609 10 Manual.Count131072.C047909.packed 64 cuts47909 = true := by
 decide +kernel
def pointBounds47909 : List (Nat × Nat × Nat) := [(6283558912,111124955483412,111125342301843)]
theorem point_links_checked47909 : (cuts47909.take 1).map (fun c => (6283460609-1+2*2^10*c.k,111124761383172+c.lower,111125148201492+c.upper)) = pointBounds47909 := by
 decide +kernel
def cuts47910 : List PrefixCut := [⟨64,262049315,262049468⟩]
theorem checked47910 : checkPrefixCuts (2^48) 6283591681 10 Manual.Count131072.C047910.packed 64 cuts47910 = true := by
 decide +kernel
def cuts47911 : List PrefixCut := [⟨16,66608934,66608972⟩,
⟨64,260834435,260834583⟩]
theorem checked47911 : checkPrefixCuts (2^48) 6283722753 10 Manual.Count131072.C047911.packed 64 cuts47911 = true := by
 decide +kernel
def pointBounds47911 : List (Nat × Nat × Nat) := [(6283755520,111125348960520,111125735779177)]
theorem point_links_checked47911 : (cuts47911.take 1).map (fun c => (6283722753-1+2*2^10*c.k,111125282351586+c.lower,111125669170205+c.upper)) = pointBounds47911 := by
 decide +kernel
def cuts47912 : List PrefixCut := [⟨48,194894364,194894477⟩,
⟨64,257559128,257559280⟩]
theorem checked47912 : checkPrefixCuts (2^48) 6283853825 10 Manual.Count131072.C047912.packed 64 cuts47912 = true := by
 decide +kernel
def pointBounds47912 : List (Nat × Nat × Nat) := [(6283952128,111125738080385,111126124899265)]
theorem point_links_checked47912 : (cuts47912.take 1).map (fun c => (6283853825-1+2*2^10*c.k,111125543186021+c.lower,111125930004788+c.upper)) = pointBounds47912 := by
 decide +kernel
def cuts47913 : List PrefixCut := [⟨64,257777698,257777846⟩]
theorem checked47913 : checkPrefixCuts (2^48) 6283984897 10 Manual.Count131072.C047913.packed 64 cuts47913 = true := by
 decide +kernel
def cuts47914 : List PrefixCut := [⟨16,63514161,63514196⟩,
⟨64,256204643,256204790⟩]
theorem checked47914 : checkPrefixCuts (2^48) 6284115969 10 Manual.Count131072.C047914.packed 64 cuts47914 = true := by
 decide +kernel
def pointBounds47914 : List (Nat × Nat × Nat) := [(6284148736,111126122037008,111126508856110)]
theorem point_links_checked47914 : (cuts47914.take 1).map (fun c => (6284115969-1+2*2^10*c.k,111126058522847+c.lower,111126445341914+c.upper)) = pointBounds47914 := by
 decide +kernel
def cuts47915 : List PrefixCut := [⟨48,196673792,196673900⟩,
⟨64,261798065,261798214⟩]
theorem checked47915 : checkPrefixCuts (2^48) 6284247041 10 Manual.Count131072.C047915.packed 64 cuts47915 = true := by
 decide +kernel
def pointBounds47915 : List (Nat × Nat × Nat) := [(6284345344,111126511401282,111126898220604)]
theorem point_links_checked47915 : (cuts47915.take 1).map (fun c => (6284247041-1+2*2^10*c.k,111126314727490+c.lower,111126701546704+c.upper)) = pointBounds47915 := by
 decide +kernel
def cuts47916 : List PrefixCut := [⟨64,257358462,257358609⟩]
theorem checked47916 : checkPrefixCuts (2^48) 6284378113 10 Manual.Count131072.C047916.packed 64 cuts47916 = true := by
 decide +kernel
def cuts47917 : List PrefixCut := [⟨16,63286245,63286284⟩,
⟨64,262548509,262548658⟩]
theorem checked47917 : checkPrefixCuts (2^48) 6284509185 10 Manual.Count131072.C047917.packed 64 cuts47917 = true := by
 decide +kernel
def pointBounds47917 : List (Nat × Nat × Nat) := [(6284541952,111126897170262,111127283989811)]
theorem point_links_checked47917 : (cuts47917.take 1).map (fun c => (6284509185-1+2*2^10*c.k,111126833884017+c.lower,111127220703527+c.upper)) = pointBounds47917 := by
 decide +kernel
def cuts47918 : List PrefixCut := [⟨48,197825952,197826061⟩,
⟨64,264334545,264334692⟩]
theorem checked47918 : checkPrefixCuts (2^48) 6284640257 10 Manual.Count131072.C047918.packed 64 cuts47918 = true := by
 decide +kernel
def pointBounds47918 : List (Nat × Nat × Nat) := [(6284738560,111127294258478,111127681078246)]
theorem point_links_checked47918 : (cuts47918.take 1).map (fun c => (6284640257-1+2*2^10*c.k,111127096432526+c.lower,111127483252185+c.upper)) = pointBounds47918 := by
 decide +kernel
def cuts47919 : List PrefixCut := [⟨64,260298273,260298425⟩]
theorem checked47919 : checkPrefixCuts (2^48) 6284771329 10 Manual.Count131072.C047919.packed 64 cuts47919 = true := by
 decide +kernel
def cuts47920 : List PrefixCut := [⟨16,65208071,65208109⟩,
⟨64,260068901,260069050⟩]
theorem checked47920 : checkPrefixCuts (2^48) 6284902401 10 Manual.Count131072.C047920.packed 64 cuts47920 = true := by
 decide +kernel
def pointBounds47920 : List (Nat × Nat × Nat) := [(6284935168,111127686273415,111128073093411)]
theorem point_links_checked47920 : (cuts47920.take 1).map (fun c => (6284902401-1+2*2^10*c.k,111127621065344+c.lower,111128007885302+c.upper)) = pointBounds47920 := by
 decide +kernel
def cuts47921 : List PrefixCut := [⟨48,194006868,194006980⟩,
⟨64,258809508,258809656⟩]
theorem checked47921 : checkPrefixCuts (2^48) 6285033473 10 Manual.Count131072.C047921.packed 64 cuts47921 = true := by
 decide +kernel
def pointBounds47921 : List (Nat × Nat × Nat) := [(6285131776,111128075141113,111128461961332)]
theorem point_links_checked47921 : (cuts47921.take 1).map (fun c => (6285033473-1+2*2^10*c.k,111127881134245+c.lower,111128267954352+c.upper)) = pointBounds47921 := by
 decide +kernel
def cuts47922 : List PrefixCut := [⟨64,264402084,264402235⟩]
theorem checked47922 : checkPrefixCuts (2^48) 6285164545 10 Manual.Count131072.C047922.packed 64 cuts47922 = true := by
 decide +kernel
def cuts47923 : List PrefixCut := [⟨16,65069646,65069683⟩,
⟨64,259873518,259873666⟩]
theorem checked47923 : checkPrefixCuts (2^48) 6285295617 10 Manual.Count131072.C047923.packed 64 cuts47923 = true := by
 decide +kernel
def pointBounds47923 : List (Nat × Nat × Nat) := [(6285328384,111128469415483,111128856235926)]
theorem point_links_checked47923 : (cuts47923.take 1).map (fun c => (6285295617-1+2*2^10*c.k,111128404345837+c.lower,111128791166243+c.upper)) = pointBounds47923 := by
 decide +kernel
def cuts47924 : List PrefixCut := [⟨48,195965122,195965234⟩,
⟨64,262465390,262465545⟩]
theorem checked47924 : checkPrefixCuts (2^48) 6285426689 10 Manual.Count131072.C047924.packed 64 cuts47924 = true := by
 decide +kernel
def pointBounds47924 : List (Nat × Nat × Nat) := [(6285524992,111128860184477,111129247005143)]
theorem point_links_checked47924 : (cuts47924.take 1).map (fun c => (6285426689-1+2*2^10*c.k,111128664219355+c.lower,111129051039909+c.upper)) = pointBounds47924 := by
 decide +kernel
def cuts47925 : List PrefixCut := [⟨64,262101685,262101838⟩]
theorem checked47925 : checkPrefixCuts (2^48) 6285557761 10 Manual.Count131072.C047925.packed 64 cuts47925 = true := by
 decide +kernel
def cuts47926 : List PrefixCut := [⟨16,60990581,60990616⟩,
⟨64,258872052,258872199⟩]
theorem checked47926 : checkPrefixCuts (2^48) 6285688833 10 Manual.Count131072.C047926.packed 64 cuts47926 = true := by
 decide +kernel
def pointBounds47926 : List (Nat × Nat × Nat) := [(6285721600,111129249777011,111129636597908)]
theorem point_links_checked47926 : (cuts47926.take 1).map (fun c => (6285688833-1+2*2^10*c.k,111129188786430+c.lower,111129575607292+c.upper)) = pointBounds47926 := by
 decide +kernel
def cuts47927 : List PrefixCut := [⟨48,195684205,195684313⟩,
⟨64,259538382,259538527⟩]
theorem checked47927 : checkPrefixCuts (2^48) 6285819905 10 Manual.Count131072.C047927.packed 64 cuts47927 = true := by
 decide +kernel
def pointBounds47927 : List (Nat × Nat × Nat) := [(6285918208,111129643342687,111130030163804)]
theorem point_links_checked47927 : (cuts47927.take 1).map (fun c => (6285819905-1+2*2^10*c.k,111129447658482+c.lower,111129834479491+c.upper)) = pointBounds47927 := by
 decide +kernel
def cuts47928 : List PrefixCut := [⟨64,259935956,259936103⟩]
theorem checked47928 : checkPrefixCuts (2^48) 6285950977 10 Manual.Count131072.C047928.packed 64 cuts47928 = true := by
 decide +kernel
def cuts47929 : List PrefixCut := [⟨16,66942150,66942190⟩,
⟨64,261676866,261677013⟩]
theorem checked47929 : checkPrefixCuts (2^48) 6286082049 10 Manual.Count131072.C047929.packed 64 cuts47929 = true := by
 decide +kernel
def pointBounds47929 : List (Nat × Nat × Nat) := [(6286114816,111130034074970,111130420896311)]
theorem point_links_checked47929 : (cuts47929.take 1).map (fun c => (6286082049-1+2*2^10*c.k,111129967132820+c.lower,111130353954121+c.upper)) = pointBounds47929 := by
 decide +kernel
def cuts47930 : List PrefixCut := [⟨48,198313751,198313864⟩,
⟨64,263104223,263104377⟩]
theorem checked47930 : checkPrefixCuts (2^48) 6286213121 10 Manual.Count131072.C047930.packed 64 cuts47930 = true := by
 decide +kernel
def pointBounds47930 : List (Nat × Nat × Nat) := [(6286311424,111130427123437,111130813944998)]
theorem point_links_checked47930 : (cuts47930.take 1).map (fun c => (6286213121-1+2*2^10*c.k,111130228809686+c.lower,111130615631134+c.upper)) = pointBounds47930 := by
 decide +kernel
def cuts47931 : List PrefixCut := [⟨64,266725551,266725702⟩]
theorem checked47931 : checkPrefixCuts (2^48) 6286344193 10 Manual.Count131072.C047931.packed 64 cuts47931 = true := by
 decide +kernel
def cuts47932 : List PrefixCut := [⟨16,64609693,64609729⟩,
⟨64,258436735,258436883⟩]
theorem checked47932 : checkPrefixCuts (2^48) 6286475265 10 Manual.Count131072.C047932.packed 64 cuts47932 = true := by
 decide +kernel
def pointBounds47932 : List (Nat × Nat × Nat) := [(6286508032,111130823249153,111131210070942)]
theorem point_links_checked47932 : (cuts47932.take 1).map (fun c => (6286475265-1+2*2^10*c.k,111130758639460+c.lower,111131145461213+c.upper)) = pointBounds47932 := by
 decide +kernel
def cuts47933 : List PrefixCut := [⟨48,193868794,193868906⟩,
⟨64,257267258,257267406⟩]
theorem checked47933 : checkPrefixCuts (2^48) 6286606337 10 Manual.Count131072.C047933.packed 64 cuts47933 = true := by
 decide +kernel
def pointBounds47933 : List (Nat × Nat × Nat) := [(6286704640,111131210944989,111131597767002)]
theorem point_links_checked47933 : (cuts47933.take 1).map (fun c => (6286606337-1+2*2^10*c.k,111131017076195+c.lower,111131403898096+c.upper)) = pointBounds47933 := by
 decide +kernel
def cuts47934 : List PrefixCut := [⟨64,260530284,260530435⟩]
theorem checked47934 : checkPrefixCuts (2^48) 6286737409 10 Manual.Count131072.C047934.packed 64 cuts47934 = true := by
 decide +kernel
def cuts47935 : List PrefixCut := [⟨16,65232450,65232489⟩,
⟨64,259763706,259763860⟩]
theorem checked47935 : checkPrefixCuts (2^48) 6286868481 10 Manual.Count131072.C047935.packed 64 cuts47935 = true := by
 decide +kernel
def pointBounds47935 : List (Nat × Nat × Nat) := [(6286901248,111131600106187,111131986928426)]
theorem point_links_checked47935 : (cuts47935.take 1).map (fun c => (6286868481-1+2*2^10*c.k,111131534873737+c.lower,111131921695937+c.upper)) = pointBounds47935 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S5.B000247
