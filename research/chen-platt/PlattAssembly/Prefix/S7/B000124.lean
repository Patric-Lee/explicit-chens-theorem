import PlattAssemblyKernel
import PlattCertificates.Count131072.C063968
import PlattCertificates.Count131072.C063969
import PlattCertificates.Count131072.C063970
import PlattCertificates.Count131072.C063971
import PlattCertificates.Count131072.C063972
import PlattCertificates.Count131072.C063973
import PlattCertificates.Count131072.C063974
import PlattCertificates.Count131072.C063975
import PlattCertificates.Count131072.C063976
import PlattCertificates.Count131072.C063977
import PlattCertificates.Count131072.C063978
import PlattCertificates.Count131072.C063979
import PlattCertificates.Count131072.C063980
import PlattCertificates.Count131072.C063981
import PlattCertificates.Count131072.C063982
import PlattCertificates.Count131072.C063983
import PlattCertificates.Count131072.C063984
import PlattCertificates.Count131072.C063985
import PlattCertificates.Count131072.C063986
import PlattCertificates.Count131072.C063987
import PlattCertificates.Count131072.C063988
import PlattCertificates.Count131072.C063989
import PlattCertificates.Count131072.C063990
import PlattCertificates.Count131072.C063991
import PlattCertificates.Count131072.C063992
import PlattCertificates.Count131072.C063993
import PlattCertificates.Count131072.C063994
import PlattCertificates.Count131072.C063995
import PlattCertificates.Count131072.C063996
import PlattCertificates.Count131072.C063997
import PlattCertificates.Count131072.C063998
import PlattCertificates.Count131072.C063999
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000124
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts63968 : List PrefixCut := [⟨48,146401662,146401749⟩,
⟨64,193445790,193445905⟩]
theorem checked63968 : checkPrefixCuts (2^48) 8388345857 10 Manual.Count131072.C063968.packed 64 cuts63968 = true := by
 decide +kernel
def pointBounds63968 : List (Nat × Nat × Nat) := [(8388444160,114706582834855,114706971695251)]
theorem point_links_checked63968 : (cuts63968.take 1).map (fun c => (8388345857-1+2*2^10*c.k,114706436433193+c.lower,114706825293502+c.upper)) = pointBounds63968 := by
 decide +kernel
def cuts63969 : List PrefixCut := [⟨64,192838763,192838880⟩]
theorem checked63969 : checkPrefixCuts (2^48) 8388476929 10 Manual.Count131072.C063969.packed 64 cuts63969 = true := by
 decide +kernel
def cuts63970 : List PrefixCut := [⟨48,141733043,141733127⟩,
⟨64,190856047,190856158⟩]
theorem checked63970 : checkPrefixCuts (2^48) 8388608001 10 Manual.Count131072.C063970.packed 64 cuts63970 = true := by
 decide +kernel
def pointBounds63970 : List (Nat × Nat × Nat) := [(8388706304,114706964450789,114707353311414)]
theorem point_links_checked63970 : (cuts63970.take 1).map (fun c => (8388608001-1+2*2^10*c.k,114706822717746+c.lower,114707211578287+c.upper)) = pointBounds63970 := by
 decide +kernel
def cuts63971 : List PrefixCut := [⟨64,194476870,194476977⟩]
theorem checked63971 : checkPrefixCuts (2^48) 8388739073 10 Manual.Count131072.C063971.packed 64 cuts63971 = true := by
 decide +kernel
def cuts63972 : List PrefixCut := [⟨49,148372129,148372217⟩,
⟨64,193400134,193400247⟩]
theorem checked63972 : checkPrefixCuts (2^48) 8388870145 10 Manual.Count131072.C063972.packed 64 cuts63972 = true := by
 decide +kernel
def pointBounds63972 : List (Nat × Nat × Nat) := [(8388970496,114707356422792,114707745283639)]
theorem point_links_checked63972 : (cuts63972.take 1).map (fun c => (8388870145-1+2*2^10*c.k,114707208050663+c.lower,114707596911422+c.upper)) = pointBounds63972 := by
 decide +kernel
def cuts63973 : List PrefixCut := [⟨64,191853688,191853802⟩]
theorem checked63973 : checkPrefixCuts (2^48) 8389001217 10 Manual.Count131072.C063973.packed 64 cuts63973 = true := by
 decide +kernel
def cuts63974 : List PrefixCut := [⟨50,150950998,150951079⟩,
⟨64,193058581,193058684⟩]
theorem checked63974 : checkPrefixCuts (2^48) 8389132289 10 Manual.Count131072.C063974.packed 64 cuts63974 = true := by
 decide +kernel
def pointBounds63974 : List (Nat × Nat × Nat) := [(8389234688,114707744255483,114708133116550)]
theorem point_links_checked63974 : (cuts63974.take 1).map (fun c => (8389132289-1+2*2^10*c.k,114707593304485+c.lower,114707982165471+c.upper)) = pointBounds63974 := by
 decide +kernel
def cuts63975 : List PrefixCut := [⟨64,193625935,193626049⟩]
theorem checked63975 : checkPrefixCuts (2^48) 8389263361 10 Manual.Count131072.C063975.packed 64 cuts63975 = true := by
 decide +kernel
def cuts63976 : List PrefixCut := [⟨51,149906170,149906253⟩,
⟨64,189361919,189362025⟩]
theorem checked63976 : checkPrefixCuts (2^48) 8389394433 10 Manual.Count131072.C063976.packed 64 cuts63976 = true := by
 decide +kernel
def pointBounds63976 : List (Nat × Nat × Nat) := [(8389498880,114708129895171,114708518756457)]
theorem point_links_checked63976 : (cuts63976.take 1).map (fun c => (8389394433-1+2*2^10*c.k,114707979989001+c.lower,114708368850204+c.upper)) = pointBounds63976 := by
 decide +kernel
def cuts63977 : List PrefixCut := [⟨64,196236835,196236952⟩]
theorem checked63977 : checkPrefixCuts (2^48) 8389525505 10 Manual.Count131072.C063977.packed 64 cuts63977 = true := by
 decide +kernel
def cuts63978 : List PrefixCut := [⟨52,155202380,155202467⟩,
⟨64,191603863,191603970⟩]
theorem checked63978 : checkPrefixCuts (2^48) 8389656577 10 Manual.Count131072.C063978.packed 64 cuts63978 = true := by
 decide +kernel
def pointBounds63978 : List (Nat × Nat × Nat) := [(8389763072,114708520790135,114708909651648)]
theorem point_links_checked63978 : (cuts63978.take 1).map (fun c => (8389656577-1+2*2^10*c.k,114708365587755+c.lower,114708754449181+c.upper)) = pointBounds63978 := by
 decide +kernel
def cuts63979 : List PrefixCut := [⟨64,192037006,192037111⟩]
theorem checked63979 : checkPrefixCuts (2^48) 8389787649 10 Manual.Count131072.C063979.packed 64 cuts63979 = true := by
 decide +kernel
def cuts63980 : List PrefixCut := [⟨53,160800192,160800282⟩,
⟨64,193476628,193476735⟩]
theorem checked63980 : checkPrefixCuts (2^48) 8389918721 10 Manual.Count131072.C063980.packed 64 cuts63980 = true := by
 decide +kernel
def pointBounds63980 : List (Nat × Nat × Nat) := [(8390027264,114708910028816,114709298890544)]
theorem point_links_checked63980 : (cuts63980.take 1).map (fun c => (8389918721-1+2*2^10*c.k,114708749228624+c.lower,114709138090262+c.upper)) = pointBounds63980 := by
 decide +kernel
def cuts63981 : List PrefixCut := [⟨64,194580681,194580788⟩]
theorem checked63981 : checkPrefixCuts (2^48) 8390049793 10 Manual.Count131072.C063981.packed 64 cuts63981 = true := by
 decide +kernel
def cuts63982 : List PrefixCut := [⟨54,160057076,160057173⟩,
⟨64,189813841,189813953⟩]
theorem checked63982 : checkPrefixCuts (2^48) 8390180865 10 Manual.Count131072.C063982.packed 64 cuts63982 = true := by
 decide +kernel
def pointBounds63982 : List (Nat × Nat × Nat) := [(8390291456,114709297343009,114709686204958)]
theorem point_links_checked63982 : (cuts63982.take 1).map (fun c => (8390180865-1+2*2^10*c.k,114709137285933+c.lower,114709526147785+c.upper)) = pointBounds63982 := by
 decide +kernel
def cuts63983 : List PrefixCut := [⟨64,192293389,192293496⟩]
theorem checked63983 : checkPrefixCuts (2^48) 8390311937 10 Manual.Count131072.C063983.packed 64 cuts63983 = true := by
 decide +kernel
def cuts63984 : List PrefixCut := [⟨55,166761438,166761534⟩,
⟨64,193229701,193229813⟩]
theorem checked63984 : checkPrefixCuts (2^48) 8390443009 10 Manual.Count131072.C063984.packed 64 cuts63984 = true := by
 decide +kernel
def pointBounds63984 : List (Nat × Nat × Nat) := [(8390555648,114709686154601,114710075016768)]
theorem point_links_checked63984 : (cuts63984.take 1).map (fun c => (8390443009-1+2*2^10*c.k,114709519393163+c.lower,114709908255234+c.upper)) = pointBounds63984 := by
 decide +kernel
def cuts63985 : List PrefixCut := [⟨64,191884811,191884923⟩]
theorem checked63985 : checkPrefixCuts (2^48) 8390574081 10 Manual.Count131072.C063985.packed 64 cuts63985 = true := by
 decide +kernel
def cuts63986 : List PrefixCut := [⟨56,166185924,166186024⟩,
⟨64,190103896,190104012⟩]
theorem checked63986 : checkPrefixCuts (2^48) 8390705153 10 Manual.Count131072.C063986.packed 64 cuts63986 = true := by
 decide +kernel
def pointBounds63986 : List (Nat × Nat × Nat) := [(8390819840,114710070693599,114710459555994)]
theorem point_links_checked63986 : (cuts63986.take 1).map (fun c => (8390705153-1+2*2^10*c.k,114709904507675+c.lower,114710293369970+c.upper)) = pointBounds63986 := by
 decide +kernel
def cuts63987 : List PrefixCut := [⟨64,193489000,193489111⟩]
theorem checked63987 : checkPrefixCuts (2^48) 8390836225 10 Manual.Count131072.C063987.packed 64 cuts63987 = true := by
 decide +kernel
def cuts63988 : List PrefixCut := [⟨57,173694740,173694838⟩,
⟨64,193519536,193519645⟩]
theorem checked63988 : checkPrefixCuts (2^48) 8390967297 10 Manual.Count131072.C063988.packed 64 cuts63988 = true := by
 decide +kernel
def pointBounds63988 : List (Nat × Nat × Nat) := [(8391084032,114710461795311,114710850657931)]
theorem point_links_checked63988 : (cuts63988.take 1).map (fun c => (8390967297-1+2*2^10*c.k,114710288100571+c.lower,114710676963093+c.upper)) = pointBounds63988 := by
 decide +kernel
def cuts63989 : List PrefixCut := [⟨64,191939909,191940015⟩]
theorem checked63989 : checkPrefixCuts (2^48) 8391098369 10 Manual.Count131072.C063989.packed 64 cuts63989 = true := by
 decide +kernel
def cuts63990 : List PrefixCut := [⟨58,173924101,173924200⟩,
⟨64,191836298,191836409⟩]
theorem checked63990 : checkPrefixCuts (2^48) 8391229441 10 Manual.Count131072.C063990.packed 64 cuts63990 = true := by
 decide +kernel
def pointBounds63990 : List (Nat × Nat × Nat) := [(8391348224,114710847484117,114711236346953)]
theorem point_links_checked63990 : (cuts63990.take 1).map (fun c => (8391229441-1+2*2^10*c.k,114710673560016+c.lower,114711062422753+c.upper)) = pointBounds63990 := by
 decide +kernel
def cuts63991 : List PrefixCut := [⟨64,190122591,190122705⟩]
theorem checked63991 : checkPrefixCuts (2^48) 8391360513 10 Manual.Count131072.C063991.packed 64 cuts63991 = true := by
 decide +kernel
def cuts63992 : List PrefixCut := [⟨59,176132451,176132555⟩,
⟨64,191025271,191025384⟩]
theorem checked63992 : checkPrefixCuts (2^48) 8391491585 10 Manual.Count131072.C063992.packed 64 cuts63992 = true := by
 decide +kernel
def pointBounds63992 : List (Nat × Nat × Nat) := [(8391612416,114711231651356,114711620514422)]
theorem point_links_checked63992 : (cuts63992.take 1).map (fun c => (8391491585-1+2*2^10*c.k,114711055518905+c.lower,114711444381867+c.upper)) = pointBounds63992 := by
 decide +kernel
def cuts63993 : List PrefixCut := [⟨64,193705662,193705775⟩]
theorem checked63993 : checkPrefixCuts (2^48) 8391622657 10 Manual.Count131072.C063993.packed 64 cuts63993 = true := by
 decide +kernel
def cuts63994 : List PrefixCut := [⟨60,178776722,178776830⟩,
⟨64,190650355,190650471⟩]
theorem checked63994 : checkPrefixCuts (2^48) 8391753729 10 Manual.Count131072.C063994.packed 64 cuts63994 = true := by
 decide +kernel
def pointBounds63994 : List (Nat × Nat × Nat) := [(8391876608,114711619026560,114712007889856)]
theorem point_links_checked63994 : (cuts63994.take 1).map (fun c => (8391753729-1+2*2^10*c.k,114711440249838+c.lower,114711829113026+c.upper)) = pointBounds63994 := by
 decide +kernel
def cuts63995 : List PrefixCut := [⟨64,191921938,191922050⟩]
theorem checked63995 : checkPrefixCuts (2^48) 8391884801 10 Manual.Count131072.C063995.packed 64 cuts63995 = true := by
 decide +kernel
def cuts63996 : List PrefixCut := [⟨61,179810885,179810990⟩,
⟨64,189034464,189034574⟩]
theorem checked63996 : checkPrefixCuts (2^48) 8392015873 10 Manual.Count131072.C063996.packed 64 cuts63996 = true := by
 decide +kernel
def pointBounds63996 : List (Nat × Nat × Nat) := [(8392140800,114712002633016,114712391496537)]
theorem point_links_checked63996 : (cuts63996.take 1).map (fun c => (8392015873-1+2*2^10*c.k,114711822822131+c.lower,114712211685547+c.upper)) = pointBounds63996 := by
 decide +kernel
def cuts63997 : List PrefixCut := [⟨64,193794188,193794300⟩]
theorem checked63997 : checkPrefixCuts (2^48) 8392146945 10 Manual.Count131072.C063997.packed 64 cuts63997 = true := by
 decide +kernel
def cuts63998 : List PrefixCut := [⟨62,187418694,187418801⟩,
⟨64,192986206,192986317⟩]
theorem checked63998 : checkPrefixCuts (2^48) 8392278017 10 Manual.Count131072.C063998.packed 64 cuts63998 = true := by
 decide +kernel
def pointBounds63998 : List (Nat × Nat × Nat) := [(8392404992,114712393069477,114712781933222)]
theorem point_links_checked63998 : (cuts63998.take 1).map (fun c => (8392278017-1+2*2^10*c.k,114712205650783+c.lower,114712594514421+c.upper)) = pointBounds63998 := by
 decide +kernel
def cuts63999 : List PrefixCut := [⟨64,190333614,190333728⟩]
theorem checked63999 : checkPrefixCuts (2^48) 8392409089 10 Manual.Count131072.C063999.packed 64 cuts63999 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000124
