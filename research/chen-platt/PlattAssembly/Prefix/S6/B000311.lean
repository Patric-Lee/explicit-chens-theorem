import PlattAssemblyKernel
import PlattCertificates.Count131072.C059952
import PlattCertificates.Count131072.C059953
import PlattCertificates.Count131072.C059954
import PlattCertificates.Count131072.C059955
import PlattCertificates.Count131072.C059956
import PlattCertificates.Count131072.C059957
import PlattCertificates.Count131072.C059958
import PlattCertificates.Count131072.C059959
import PlattCertificates.Count131072.C059960
import PlattCertificates.Count131072.C059961
import PlattCertificates.Count131072.C059962
import PlattCertificates.Count131072.C059963
import PlattCertificates.Count131072.C059964
import PlattCertificates.Count131072.C059965
import PlattCertificates.Count131072.C059966
import PlattCertificates.Count131072.C059967
import PlattCertificates.Count131072.C059968
import PlattCertificates.Count131072.C059969
import PlattCertificates.Count131072.C059970
import PlattCertificates.Count131072.C059971
import PlattCertificates.Count131072.C059972
import PlattCertificates.Count131072.C059973
import PlattCertificates.Count131072.C059974
import PlattCertificates.Count131072.C059975
import PlattCertificates.Count131072.C059976
import PlattCertificates.Count131072.C059977
import PlattCertificates.Count131072.C059978
import PlattCertificates.Count131072.C059979
import PlattCertificates.Count131072.C059980
import PlattCertificates.Count131072.C059981
import PlattCertificates.Count131072.C059982
import PlattCertificates.Count131072.C059983
namespace ChenEffective.PlattWindow.Assembly.Prefix.S6.B000311
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts59952 : List PrefixCut := [⟨64,207292569,207292687⟩]
theorem checked59952 : checkPrefixCuts (2^48) 7861960705 10 Manual.Count131072.C059952.packed 64 cuts59952 = true := by
 decide +kernel
def cuts59953 : List PrefixCut := [⟨47,153229607,153229692⟩,
⟨64,207790349,207790465⟩]
theorem checked59953 : checkPrefixCuts (2^48) 7862091777 10 Manual.Count131072.C059953.packed 64 cuts59953 = true := by
 decide +kernel
def pointBounds59953 : List (Nat × Nat × Nat) := [(7862188032,113907271358061,113907659759819)]
theorem point_links_checked59953 : (cuts59953.take 1).map (fun c => (7862091777-1+2*2^10*c.k,113907118128454+c.lower,113907506530127+c.upper)) = pointBounds59953 := by
 decide +kernel
def cuts59954 : List PrefixCut := [⟨64,204708020,204708134⟩]
theorem checked59954 : checkPrefixCuts (2^48) 7862222849 10 Manual.Count131072.C059954.packed 64 cuts59954 = true := by
 decide +kernel
def cuts59955 : List PrefixCut := [⟨39,127412745,127412815⟩,
⟨64,206709420,206709538⟩]
theorem checked59955 : checkPrefixCuts (2^48) 7862353921 10 Manual.Count131072.C059955.packed 64 cuts59955 = true := by
 decide +kernel
def pointBounds59955 : List (Nat × Nat × Nat) := [(7862433792,113907658039568,113908046441541)]
theorem point_links_checked59955 : (cuts59955.take 1).map (fun c => (7862353921-1+2*2^10*c.k,113907530626823+c.lower,113907919028726+c.upper)) = pointBounds59955 := by
 decide +kernel
def cuts59956 : List PrefixCut := [⟨64,206455363,206455483⟩]
theorem checked59956 : checkPrefixCuts (2^48) 7862484993 10 Manual.Count131072.C059956.packed 64 cuts59956 = true := by
 decide +kernel
def cuts59957 : List PrefixCut := [⟨31,101454352,101454410⟩,
⟨64,206165543,206165661⟩]
theorem checked59957 : checkPrefixCuts (2^48) 7862616065 10 Manual.Count131072.C059957.packed 64 cuts59957 = true := by
 decide +kernel
def pointBounds59957 : List (Nat × Nat × Nat) := [(7862679552,113908045245958,113908433648157)]
theorem point_links_checked59957 : (cuts59957.take 1).map (fun c => (7862616065-1+2*2^10*c.k,113907943791606+c.lower,113908332193747+c.upper)) = pointBounds59957 := by
 decide +kernel
def cuts59958 : List PrefixCut := [⟨64,206305278,206305395⟩]
theorem checked59958 : checkPrefixCuts (2^48) 7862747137 10 Manual.Count131072.C059958.packed 64 cuts59958 = true := by
 decide +kernel
def cuts59959 : List PrefixCut := [⟨23,73922537,73922577⟩,
⟨64,205156325,205156439⟩]
theorem checked59959 : checkPrefixCuts (2^48) 7862878209 10 Manual.Count131072.C059959.packed 64 cuts59959 = true := by
 decide +kernel
def pointBounds59959 : List (Nat × Nat × Nat) := [(7862925312,113908430184964,113908818587380)]
theorem point_links_checked59959 : (cuts59959.take 1).map (fun c => (7862878209-1+2*2^10*c.k,113908356262427+c.lower,113908744664803+c.upper)) = pointBounds59959 := by
 decide +kernel
def cuts59960 : List PrefixCut := [⟨64,202682924,202683039⟩]
theorem checked59960 : checkPrefixCuts (2^48) 7863009281 10 Manual.Count131072.C059960.packed 64 cuts59960 = true := by
 decide +kernel
def cuts59961 : List PrefixCut := [⟨15,47466404,47466431⟩,
⟨64,204218778,204218893⟩]
theorem checked59961 : checkPrefixCuts (2^48) 7863140353 10 Manual.Count131072.C059961.packed 64 cuts59961 = true := by
 decide +kernel
def pointBounds59961 : List (Nat × Nat × Nat) := [(7863171072,113908811568080,113909199970712)]
theorem point_links_checked59961 : (cuts59961.take 1).map (fun c => (7863140353-1+2*2^10*c.k,113908764101676+c.lower,113909152504281+c.upper)) = pointBounds59961 := by
 decide +kernel
def cuts59962 : List PrefixCut := [⟨64,207079040,207079161⟩]
theorem checked59962 : checkPrefixCuts (2^48) 7863271425 10 Manual.Count131072.C059962.packed 64 cuts59962 = true := by
 decide +kernel
def cuts59963 : List PrefixCut := [⟨7,22873342,22873355⟩,
⟨64,208256846,208256962⟩]
theorem checked59963 : checkPrefixCuts (2^48) 7863402497 10 Manual.Count131072.C059963.packed 64 cuts59963 = true := by
 decide +kernel
def pointBounds59963 : List (Nat × Nat × Nat) := [(7863416832,113909198272836,113909586675690)]
theorem point_links_checked59963 : (cuts59963.take 1).map (fun c => (7863402497-1+2*2^10*c.k,113909175399494+c.lower,113909563802335+c.upper)) = pointBounds59963 := by
 decide +kernel
def cuts59964 : List PrefixCut := [⟨63,201917724,201917841⟩,
⟨64,204817068,204817187⟩]
theorem checked59964 : checkPrefixCuts (2^48) 7863533569 10 Manual.Count131072.C059964.packed 64 cuts59964 = true := by
 decide +kernel
def pointBounds59964 : List (Nat × Nat × Nat) := [(7863662592,113909585574064,113909973977138)]
theorem point_links_checked59964 : (cuts59964.take 1).map (fun c => (7863533569-1+2*2^10*c.k,113909383656340+c.lower,113909772059297+c.upper)) = pointBounds59964 := by
 decide +kernel
def cuts59965 : List PrefixCut := [⟨64,205529537,205529654⟩]
theorem checked59965 : checkPrefixCuts (2^48) 7863664641 10 Manual.Count131072.C059965.packed 64 cuts59965 = true := by
 decide +kernel
def cuts59966 : List PrefixCut := [⟨55,178609634,178609731⟩,
⟨64,208425380,208425495⟩]
theorem checked59966 : checkPrefixCuts (2^48) 7863795713 10 Manual.Count131072.C059966.packed 64 cuts59966 = true := by
 decide +kernel
def pointBounds59966 : List (Nat × Nat × Nat) := [(7863908352,113909972612579,113910361015869)]
theorem point_links_checked59966 : (cuts59966.take 1).map (fun c => (7863795713-1+2*2^10*c.k,113909794002945+c.lower,113910182406138+c.upper)) = pointBounds59966 := by
 decide +kernel
def cuts59967 : List PrefixCut := [⟨64,205057400,205057515⟩]
theorem checked59967 : checkPrefixCuts (2^48) 7863926785 10 Manual.Count131072.C059967.packed 64 cuts59967 = true := by
 decide +kernel
def cuts59968 : List PrefixCut := [⟨47,153835548,153835638⟩,
⟨64,209420616,209420737⟩]
theorem checked59968 : checkPrefixCuts (2^48) 7864057857 10 Manual.Count131072.C059968.packed 64 cuts59968 = true := by
 decide +kernel
def pointBounds59968 : List (Nat × Nat × Nat) := [(7864154112,113910361321273,113910749724786)]
theorem point_links_checked59968 : (cuts59968.take 1).map (fun c => (7864057857-1+2*2^10*c.k,113910207485725+c.lower,113910595889148+c.upper)) = pointBounds59968 := by
 decide +kernel
def cuts59969 : List PrefixCut := [⟨64,206195884,206196001⟩]
theorem checked59969 : checkPrefixCuts (2^48) 7864188929 10 Manual.Count131072.C059969.packed 64 cuts59969 = true := by
 decide +kernel
def cuts59970 : List PrefixCut := [⟨39,126486111,126486183⟩,
⟨64,205548220,205548340⟩]
theorem checked59970 : checkPrefixCuts (2^48) 7864320001 10 Manual.Count131072.C059970.packed 64 cuts59970 = true := by
 decide +kernel
def pointBounds59970 : List (Nat × Nat × Nat) := [(7864399872,113910749588336,113911137992069)]
theorem point_links_checked59970 : (cuts59970.take 1).map (fun c => (7864320001-1+2*2^10*c.k,113910623102225+c.lower,113911011505886+c.upper)) = pointBounds59970 := by
 decide +kernel
def cuts59971 : List PrefixCut := [⟨64,208229056,208229173⟩]
theorem checked59971 : checkPrefixCuts (2^48) 7864451073 10 Manual.Count131072.C059971.packed 64 cuts59971 = true := by
 decide +kernel
def cuts59972 : List PrefixCut := [⟨32,102001619,102001677⟩,
⟨64,206185559,206185677⟩]
theorem checked59972 : checkPrefixCuts (2^48) 7864582145 10 Manual.Count131072.C059972.packed 64 cuts59972 = true := by
 decide +kernel
def pointBounds59972 : List (Nat × Nat × Nat) := [(7864647680,113911138881120,113911527285076)]
theorem point_links_checked59972 : (cuts59972.take 1).map (fun c => (7864582145-1+2*2^10*c.k,113911036879501+c.lower,113911425283399+c.upper)) = pointBounds59972 := by
 decide +kernel
def cuts59973 : List PrefixCut := [⟨64,206754771,206754893⟩]
theorem checked59973 : checkPrefixCuts (2^48) 7864713217 10 Manual.Count131072.C059973.packed 64 cuts59973 = true := by
 decide +kernel
def cuts59974 : List PrefixCut := [⟨25,82314426,82314473⟩,
⟨64,206536601,206536721⟩]
theorem checked59974 : checkPrefixCuts (2^48) 7864844289 10 Manual.Count131072.C059974.packed 64 cuts59974 = true := by
 decide +kernel
def pointBounds59974 : List (Nat × Nat × Nat) := [(7864895488,113911532134257,113911920538442)]
theorem point_links_checked59974 : (cuts59974.take 1).map (fun c => (7864844289-1+2*2^10*c.k,113911449819831+c.lower,113911838223969+c.upper)) = pointBounds59974 := by
 decide +kernel
def cuts59975 : List PrefixCut := [⟨64,205495291,205495407⟩]
theorem checked59975 : checkPrefixCuts (2^48) 7864975361 10 Manual.Count131072.C059975.packed 64 cuts59975 = true := by
 decide +kernel
def cuts59976 : List PrefixCut := [⟨18,58620287,58620322⟩,
⟨64,207138091,207138207⟩]
theorem checked59976 : checkPrefixCuts (2^48) 7865106433 10 Manual.Count131072.C059976.packed 64 cuts59976 = true := by
 decide +kernel
def pointBounds59976 : List (Nat × Nat × Nat) := [(7865143296,113911920472010,113912308876419)]
theorem point_links_checked59976 : (cuts59976.take 1).map (fun c => (7865106433-1+2*2^10*c.k,113911861851723+c.lower,113912250256097+c.upper)) = pointBounds59976 := by
 decide +kernel
def cuts59977 : List PrefixCut := [⟨64,204880053,204880171⟩]
theorem checked59977 : checkPrefixCuts (2^48) 7865237505 10 Manual.Count131072.C059977.packed 64 cuts59977 = true := by
 decide +kernel
def cuts59978 : List PrefixCut := [⟨11,36430720,36430741⟩,
⟨64,208061653,208061771⟩]
theorem checked59978 : checkPrefixCuts (2^48) 7865368577 10 Manual.Count131072.C059978.packed 64 cuts59978 = true := by
 decide +kernel
def pointBounds59978 : List (Nat × Nat × Nat) := [(7865391104,113912310300587,113912698705216)]
theorem point_links_checked59978 : (cuts59978.take 1).map (fun c => (7865368577-1+2*2^10*c.k,113912273869867+c.lower,113912662274475+c.upper)) = pointBounds59978 := by
 decide +kernel
def cuts59979 : List PrefixCut := [⟨64,206233085,206233202⟩]
theorem checked59979 : checkPrefixCuts (2^48) 7865499649 10 Manual.Count131072.C059979.packed 64 cuts59979 = true := by
 decide +kernel
def cuts59980 : List PrefixCut := [⟨4,13025886,13025894⟩,
⟨64,202293286,202293408⟩]
theorem checked59980 : checkPrefixCuts (2^48) 7865630721 10 Manual.Count131072.C059980.packed 64 cuts59980 = true := by
 decide +kernel
def pointBounds59980 : List (Nat × Nat × Nat) := [(7865638912,113912701190491,113913089595342)]
theorem point_links_checked59980 : (cuts59980.take 1).map (fun c => (7865630721-1+2*2^10*c.k,113912688164605+c.lower,113913076569448+c.upper)) = pointBounds59980 := by
 decide +kernel
def cuts59981 : List PrefixCut := [⟨61,196349758,196349874⟩,
⟨64,206047287,206047409⟩]
theorem checked59981 : checkPrefixCuts (2^48) 7865761793 10 Manual.Count131072.C059981.packed 64 cuts59981 = true := by
 decide +kernel
def pointBounds59981 : List (Nat × Nat × Nat) := [(7865886720,113913086807649,113913475212730)]
theorem point_links_checked59981 : (cuts59981.take 1).map (fun c => (7865761793-1+2*2^10*c.k,113912890457891+c.lower,113913278862856+c.upper)) = pointBounds59981 := by
 decide +kernel
def cuts59982 : List PrefixCut := [⟨64,207833057,207833181⟩]
theorem checked59982 : checkPrefixCuts (2^48) 7865892865 10 Manual.Count131072.C059982.packed 64 cuts59982 = true := by
 decide +kernel
def cuts59983 : List PrefixCut := [⟨54,174265053,174265154⟩,
⟨64,205861514,205861634⟩]
theorem checked59983 : checkPrefixCuts (2^48) 7866023937 10 Manual.Count131072.C059983.packed 64 cuts59983 = true := by
 decide +kernel
def pointBounds59983 : List (Nat × Nat × Nat) := [(7866134528,113913478603288,113913867008600)]
theorem point_links_checked59983 : (cuts59983.take 1).map (fun c => (7866023937-1+2*2^10*c.k,113913304338235+c.lower,113913692743446+c.upper)) = pointBounds59983 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S6.B000311
