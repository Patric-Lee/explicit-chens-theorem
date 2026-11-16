import PlattAssemblyKernel
import PlattCertificates.Count131072.C051920
import PlattCertificates.Count131072.C051921
import PlattCertificates.Count131072.C051922
import PlattCertificates.Count131072.C051923
import PlattCertificates.Count131072.C051924
import PlattCertificates.Count131072.C051925
import PlattCertificates.Count131072.C051926
import PlattCertificates.Count131072.C051927
import PlattCertificates.Count131072.C051928
import PlattCertificates.Count131072.C051929
import PlattCertificates.Count131072.C051930
import PlattCertificates.Count131072.C051931
import PlattCertificates.Count131072.C051932
import PlattCertificates.Count131072.C051933
import PlattCertificates.Count131072.C051934
import PlattCertificates.Count131072.C051935
import PlattCertificates.Count131072.C051936
import PlattCertificates.Count131072.C051937
import PlattCertificates.Count131072.C051938
import PlattCertificates.Count131072.C051939
import PlattCertificates.Count131072.C051940
import PlattCertificates.Count131072.C051941
import PlattCertificates.Count131072.C051942
import PlattCertificates.Count131072.C051943
import PlattCertificates.Count131072.C051944
import PlattCertificates.Count131072.C051945
import PlattCertificates.Count131072.C051946
import PlattCertificates.Count131072.C051947
import PlattCertificates.Count131072.C051948
import PlattCertificates.Count131072.C051949
import PlattCertificates.Count131072.C051950
import PlattCertificates.Count131072.C051951
namespace ChenEffective.PlattWindow.Assembly.Prefix.S6.B000060
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts51920 : List PrefixCut := [⟨64,239011122,239011256⟩]
theorem checked51920 : checkPrefixCuts (2^48) 6809190401 10 Manual.Count131072.C051920.packed 64 cuts51920 = true := by
 decide +kernel
def cuts51921 : List PrefixCut := [⟨35,131450025,131450098⟩,
⟨64,241197341,241197476⟩]
theorem checked51921 : checkPrefixCuts (2^48) 6809321473 10 Manual.Count131072.C051921.packed 64 cuts51921 = true := by
 decide +kernel
def pointBounds51921 : List (Nat × Nat × Nat) := [(6809393152,112125796359190,112126183747898)]
theorem point_links_checked51921 : (cuts51921.take 1).map (fun c => (6809321473-1+2*2^10*c.k,112125664909165+c.lower,112126052297800+c.upper)) = pointBounds51921 := by
 decide +kernel
def cuts51922 : List PrefixCut := [⟨64,241647375,241647510⟩]
theorem checked51922 : checkPrefixCuts (2^48) 6809452545 10 Manual.Count131072.C051922.packed 64 cuts51922 = true := by
 decide +kernel
def cuts51923 : List PrefixCut := [⟨11,41665723,41665745⟩,
⟨64,240361354,240361491⟩]
theorem checked51923 : checkPrefixCuts (2^48) 6809583617 10 Manual.Count131072.C051923.packed 64 cuts51923 = true := by
 decide +kernel
def pointBounds51923 : List (Nat × Nat × Nat) := [(6809606144,112126189419604,112126576808531)]
theorem point_links_checked51923 : (cuts51923.take 1).map (fun c => (6809583617-1+2*2^10*c.k,112126147753881+c.lower,112126535142786+c.upper)) = pointBounds51923 := by
 decide +kernel
def cuts51924 : List PrefixCut := [⟨51,192285763,192285872⟩,
⟨64,239571404,239571541⟩]
theorem checked51924 : checkPrefixCuts (2^48) 6809714689 10 Manual.Count131072.C051924.packed 64 cuts51924 = true := by
 decide +kernel
def pointBounds51924 : List (Nat × Nat × Nat) := [(6809819136,112126580400998,112126967790149)]
theorem point_links_checked51924 : (cuts51924.take 1).map (fun c => (6809714689-1+2*2^10*c.k,112126388115235+c.lower,112126775504277+c.upper)) = pointBounds51924 := by
 decide +kernel
def cuts51925 : List PrefixCut := [⟨64,236962789,236962925⟩]
theorem checked51925 : checkPrefixCuts (2^48) 6809845761 10 Manual.Count131072.C051925.packed 64 cuts51925 = true := by
 decide +kernel
def cuts51926 : List PrefixCut := [⟨27,100975439,100975495⟩,
⟨64,239396839,239396979⟩]
theorem checked51926 : checkPrefixCuts (2^48) 6809976833 10 Manual.Count131072.C051926.packed 64 cuts51926 = true := by
 decide +kernel
def pointBounds51926 : List (Nat × Nat × Nat) := [(6810032128,112126965624867,112127353014238)]
theorem point_links_checked51926 : (cuts51926.take 1).map (fun c => (6809976833-1+2*2^10*c.k,112126864649428+c.lower,112127252038743+c.upper)) = pointBounds51926 := by
 decide +kernel
def cuts51927 : List PrefixCut := [⟨64,244021348,244021483⟩]
theorem checked51927 : checkPrefixCuts (2^48) 6810107905 10 Manual.Count131072.C051927.packed 64 cuts51927 = true := by
 decide +kernel
def cuts51928 : List PrefixCut := [⟨3,10994077,10994083⟩,
⟨64,244140667,244140806⟩]
theorem checked51928 : checkPrefixCuts (2^48) 6810238977 10 Manual.Count131072.C051928.packed 64 cuts51928 = true := by
 decide +kernel
def pointBounds51928 : List (Nat × Nat × Nat) := [(6810245120,112127359061692,112127746451288)]
theorem point_links_checked51928 : (cuts51928.take 1).map (fun c => (6810238977-1+2*2^10*c.k,112127348067615+c.lower,112127735457205+c.upper)) = pointBounds51928 := by
 decide +kernel
def cuts51929 : List PrefixCut := [⟨43,159120766,159120860⟩,
⟨64,237481832,237481972⟩]
theorem checked51929 : checkPrefixCuts (2^48) 6810370049 10 Manual.Count131072.C051929.packed 64 cuts51929 = true := by
 decide +kernel
def pointBounds51929 : List (Nat × Nat × Nat) := [(6810458112,112127751329048,112128138718871)]
theorem point_links_checked51929 : (cuts51929.take 1).map (fun c => (6810370049-1+2*2^10*c.k,112127592208282+c.lower,112127979598011+c.upper)) = pointBounds51929 := by
 decide +kernel
def cuts51930 : List PrefixCut := [⟨64,239047761,239047901⟩]
theorem checked51930 : checkPrefixCuts (2^48) 6810501121 10 Manual.Count131072.C051930.packed 64 cuts51930 = true := by
 decide +kernel
def cuts51931 : List PrefixCut := [⟨19,71167899,71167937⟩,
⟨64,237927295,237927429⟩]
theorem checked51931 : checkPrefixCuts (2^48) 6810632193 10 Manual.Count131072.C051931.packed 64 cuts51931 = true := by
 decide +kernel
def pointBounds51931 : List (Nat × Nat × Nat) := [(6810671104,112128139905774,112128527295821)]
theorem point_links_checked51931 : (cuts51931.take 1).map (fun c => (6810632193-1+2*2^10*c.k,112128068737875+c.lower,112128456127884+c.upper)) = pointBounds51931 := by
 decide +kernel
def cuts51932 : List PrefixCut := [⟨59,221061256,221061381⟩,
⟨64,240402380,240402516⟩]
theorem checked51932 : checkPrefixCuts (2^48) 6810763265 10 Manual.Count131072.C051932.packed 64 cuts51932 = true := by
 decide +kernel
def pointBounds51932 : List (Nat × Nat × Nat) := [(6810884096,112128527726426,112128915116694)]
theorem point_links_checked51932 : (cuts51932.take 1).map (fun c => (6810763265-1+2*2^10*c.k,112128306665170+c.lower,112128694055313+c.upper)) = pointBounds51932 := by
 decide +kernel
def cuts51933 : List PrefixCut := [⟨64,240191113,240191247⟩]
theorem checked51933 : checkPrefixCuts (2^48) 6810894337 10 Manual.Count131072.C051933.packed 64 cuts51933 = true := by
 decide +kernel
def cuts51934 : List PrefixCut := [⟨35,132202332,132202406⟩,
⟨64,240227835,240227972⟩]
theorem checked51934 : checkPrefixCuts (2^48) 6811025409 10 Manual.Count131072.C051934.packed 64 cuts51934 = true := by
 decide +kernel
def pointBounds51934 : List (Nat × Nat × Nat) := [(6811097088,112128919460995,112129306851482)]
theorem point_links_checked51934 : (cuts51934.take 1).map (fun c => (6811025409-1+2*2^10*c.k,112128787258663+c.lower,112129174649076+c.upper)) = pointBounds51934 := by
 decide +kernel
def cuts51935 : List PrefixCut := [⟨64,241628267,241628400⟩]
theorem checked51935 : checkPrefixCuts (2^48) 6811156481 10 Manual.Count131072.C051935.packed 64 cuts51935 = true := by
 decide +kernel
def cuts51936 : List PrefixCut := [⟨11,41076754,41076777⟩,
⟨64,242656713,242656853⟩]
theorem checked51936 : checkPrefixCuts (2^48) 6811287553 10 Manual.Count131072.C051936.packed 64 cuts51936 = true := by
 decide +kernel
def pointBounds51936 : List (Nat × Nat × Nat) := [(6811310080,112129310191519,112129697582225)]
theorem point_links_checked51936 : (cuts51936.take 1).map (fun c => (6811287553-1+2*2^10*c.k,112129269114765+c.lower,112129656505448+c.upper)) = pointBounds51936 := by
 decide +kernel
def cuts51937 : List PrefixCut := [⟨51,192155034,192155141⟩,
⟨64,242238829,242238964⟩]
theorem checked51937 : checkPrefixCuts (2^48) 6811418625 10 Manual.Count131072.C051937.packed 64 cuts51937 = true := by
 decide +kernel
def pointBounds51937 : List (Nat × Nat × Nat) := [(6811523072,112129703926512,112130091317442)]
theorem point_links_checked51937 : (cuts51937.take 1).map (fun c => (6811418625-1+2*2^10*c.k,112129511771478+c.lower,112129899162301+c.upper)) = pointBounds51937 := by
 decide +kernel
def cuts51938 : List PrefixCut := [⟨64,240415954,240416089⟩]
theorem checked51938 : checkPrefixCuts (2^48) 6811549697 10 Manual.Count131072.C051938.packed 64 cuts51938 = true := by
 decide +kernel
def cuts51939 : List PrefixCut := [⟨27,101446047,101446104⟩,
⟨64,238262595,238262730⟩]
theorem checked51939 : checkPrefixCuts (2^48) 6811680769 10 Manual.Count131072.C051939.packed 64 cuts51939 = true := by
 decide +kernel
def pointBounds51939 : List (Nat × Nat × Nat) := [(6811736064,112130095872308,112130483263458)]
theorem point_links_checked51939 : (cuts51939.take 1).map (fun c => (6811680769-1+2*2^10*c.k,112129994426261+c.lower,112130381817354+c.upper)) = pointBounds51939 := by
 decide +kernel
def cuts51940 : List PrefixCut := [⟨64,240076125,240076256⟩]
theorem checked51940 : checkPrefixCuts (2^48) 6811811841 10 Manual.Count131072.C051940.packed 64 cuts51940 = true := by
 decide +kernel
def cuts51941 : List PrefixCut := [⟨3,11239252,11239258⟩,
⟨64,236600596,236600730⟩]
theorem checked51941 : checkPrefixCuts (2^48) 6811942913 10 Manual.Count131072.C051941.packed 64 cuts51941 = true := by
 decide +kernel
def pointBounds51941 : List (Nat × Nat × Nat) := [(6811949056,112130484004233,112130871395598)]
theorem point_links_checked51941 : (cuts51941.take 1).map (fun c => (6811942913-1+2*2^10*c.k,112130472764981+c.lower,112130860156340+c.upper)) = pointBounds51941 := by
 decide +kernel
def cuts51942 : List PrefixCut := [⟨43,160816401,160816490⟩,
⟨64,238662031,238662165⟩]
theorem checked51942 : checkPrefixCuts (2^48) 6812073985 10 Manual.Count131072.C051942.packed 64 cuts51942 = true := by
 decide +kernel
def pointBounds51942 : List (Nat × Nat × Nat) := [(6812162048,112130870181978,112131257573560)]
theorem point_links_checked51942 : (cuts51942.take 1).map (fun c => (6812073985-1+2*2^10*c.k,112130709365577+c.lower,112131096757070+c.upper)) = pointBounds51942 := by
 decide +kernel
def cuts51943 : List PrefixCut := [⟨64,238946669,238946808⟩]
theorem checked51943 : checkPrefixCuts (2^48) 6812205057 10 Manual.Count131072.C051943.packed 64 cuts51943 = true := by
 decide +kernel
def cuts51944 : List PrefixCut := [⟨19,70736917,70736957⟩,
⟨64,237248029,237248165⟩]
theorem checked51944 : checkPrefixCuts (2^48) 6812336129 10 Manual.Count131072.C051944.packed 64 cuts51944 = true := by
 decide +kernel
def pointBounds51944 : List (Nat × Nat × Nat) := [(6812375040,112131257711194,112131645103000)]
theorem point_links_checked51944 : (cuts51944.take 1).map (fun c => (6812336129-1+2*2^10*c.k,112131186974277+c.lower,112131574366043+c.upper)) = pointBounds51944 := by
 decide +kernel
def cuts51945 : List PrefixCut := [⟨59,222989189,222989315⟩,
⟨64,241416505,241416641⟩]
theorem checked51945 : checkPrefixCuts (2^48) 6812467201 10 Manual.Count131072.C051945.packed 64 cuts51945 = true := by
 decide +kernel
def pointBounds51945 : List (Nat × Nat × Nat) := [(6812588032,112131647211495,112132034603523)]
theorem point_links_checked51945 : (cuts51945.take 1).map (fun c => (6812467201-1+2*2^10*c.k,112131424222306+c.lower,112131811614208+c.upper)) = pointBounds51945 := by
 decide +kernel
def cuts51946 : List PrefixCut := [⟨64,237445492,237445626⟩]
theorem checked51946 : checkPrefixCuts (2^48) 6812598273 10 Manual.Count131072.C051946.packed 64 cuts51946 = true := by
 decide +kernel
def cuts51947 : List PrefixCut := [⟨35,132003995,132004071⟩,
⟨64,238432495,238432631⟩]
theorem checked51947 : checkPrefixCuts (2^48) 6812729345 10 Manual.Count131072.C051947.packed 64 cuts51947 = true := by
 decide +kernel
def pointBounds51947 : List (Nat × Nat × Nat) := [(6812801024,112132035088298,112132422480546)]
theorem point_links_checked51947 : (cuts51947.take 1).map (fun c => (6812729345-1+2*2^10*c.k,112131903084303+c.lower,112132290476475+c.upper)) = pointBounds51947 := by
 decide +kernel
def cuts51948 : List PrefixCut := [⟨64,237271078,237271212⟩]
theorem checked51948 : checkPrefixCuts (2^48) 6812860417 10 Manual.Count131072.C051948.packed 64 cuts51948 = true := by
 decide +kernel
def cuts51949 : List PrefixCut := [⟨11,39455220,39455243⟩,
⟨64,238836440,238836576⟩]
theorem checked51949 : checkPrefixCuts (2^48) 6812991489 10 Manual.Count131072.C051949.packed 64 cuts51949 = true := by
 decide +kernel
def pointBounds51949 : List (Nat × Nat × Nat) := [(6813014016,112132418243096,112132805635561)]
theorem point_links_checked51949 : (cuts51949.take 1).map (fun c => (6812991489-1+2*2^10*c.k,112132378787876+c.lower,112132766180318+c.upper)) = pointBounds51949 := by
 decide +kernel
def cuts51950 : List PrefixCut := [⟨51,190289160,190289271⟩,
⟨64,236477014,236477151⟩]
theorem checked51950 : checkPrefixCuts (2^48) 6813122561 10 Manual.Count131072.C051950.packed 64 cuts51950 = true := by
 decide +kernel
def pointBounds51950 : List (Nat × Nat × Nat) := [(6813227008,112132807913476,112133195306165)]
theorem point_links_checked51950 : (cuts51950.take 1).map (fun c => (6813122561-1+2*2^10*c.k,112132617624316+c.lower,112133005016894+c.upper)) = pointBounds51950 := by
 decide +kernel
def cuts51951 : List PrefixCut := [⟨64,238124946,238125081⟩]
theorem checked51951 : checkPrefixCuts (2^48) 6813253633 10 Manual.Count131072.C051951.packed 64 cuts51951 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S6.B000060
