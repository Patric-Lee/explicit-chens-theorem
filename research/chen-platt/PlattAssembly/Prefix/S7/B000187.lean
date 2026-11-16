import PlattAssemblyKernel
import PlattCertificates.Count131072.C065984
import PlattCertificates.Count131072.C065985
import PlattCertificates.Count131072.C065986
import PlattCertificates.Count131072.C065987
import PlattCertificates.Count131072.C065988
import PlattCertificates.Count131072.C065989
import PlattCertificates.Count131072.C065990
import PlattCertificates.Count131072.C065991
import PlattCertificates.Count131072.C065992
import PlattCertificates.Count131072.C065993
import PlattCertificates.Count131072.C065994
import PlattCertificates.Count131072.C065995
import PlattCertificates.Count131072.C065996
import PlattCertificates.Count131072.C065997
import PlattCertificates.Count131072.C065998
import PlattCertificates.Count131072.C065999
import PlattCertificates.Count131072.C066000
import PlattCertificates.Count131072.C066001
import PlattCertificates.Count131072.C066002
import PlattCertificates.Count131072.C066003
import PlattCertificates.Count131072.C066004
import PlattCertificates.Count131072.C066005
import PlattCertificates.Count131072.C066006
import PlattCertificates.Count131072.C066007
import PlattCertificates.Count131072.C066008
import PlattCertificates.Count131072.C066009
import PlattCertificates.Count131072.C066010
import PlattCertificates.Count131072.C066011
import PlattCertificates.Count131072.C066012
import PlattCertificates.Count131072.C066013
import PlattCertificates.Count131072.C066014
import PlattCertificates.Count131072.C066015
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000187
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts65984 : List PrefixCut := [⟨64,184415269,184415374⟩]
theorem checked65984 : checkPrefixCuts (2^48) 8652587009 10 Manual.Count131072.C065984.packed 64 cuts65984 = true := by
 decide +kernel
def cuts65985 : List PrefixCut := [⟨30,86042152,86042207⟩,
⟨64,184379943,184380051⟩]
theorem checked65985 : checkPrefixCuts (2^48) 8652718081 10 Manual.Count131072.C065985.packed 64 cuts65985 = true := by
 decide +kernel
def pointBounds65985 : List (Nat × Nat × Nat) := [(8652779520,115088495881475,115088884962838)]
theorem point_links_checked65985 : (cuts65985.take 1).map (fun c => (8652718081-1+2*2^10*c.k,115088409839323+c.lower,115088798920631+c.upper)) = pointBounds65985 := by
 decide +kernel
def cuts65986 : List PrefixCut := [⟨64,185840972,185841080⟩]
theorem checked65986 : checkPrefixCuts (2^48) 8652849153 10 Manual.Count131072.C065986.packed 64 cuts65986 = true := by
 decide +kernel
def cuts65987 : List PrefixCut := [⟨35,104028087,104028144⟩,
⟨64,187659791,187659893⟩]
theorem checked65987 : checkPrefixCuts (2^48) 8652980225 10 Manual.Count131072.C065987.packed 64 cuts65987 = true := by
 decide +kernel
def pointBounds65987 : List (Nat × Nat × Nat) := [(8653051904,115088884088325,115089273169906)]
theorem point_links_checked65987 : (cuts65987.take 1).map (fun c => (8652980225-1+2*2^10*c.k,115088780060238+c.lower,115089169141762+c.upper)) = pointBounds65987 := by
 decide +kernel
def cuts65988 : List PrefixCut := [⟨64,186518438,186518552⟩]
theorem checked65988 : checkPrefixCuts (2^48) 8653111297 10 Manual.Count131072.C065988.packed 64 cuts65988 = true := by
 decide +kernel
def cuts65989 : List PrefixCut := [⟨40,119280554,119280623⟩,
⟨64,188434780,188434892⟩]
theorem checked65989 : checkPrefixCuts (2^48) 8653242369 10 Manual.Count131072.C065989.packed 64 cuts65989 = true := by
 decide +kernel
def pointBounds65989 : List (Nat × Nat × Nat) := [(8653324288,115089273519021,115089662600830)]
theorem point_links_checked65989 : (cuts65989.take 1).map (fun c => (8653242369-1+2*2^10*c.k,115089154238467+c.lower,115089543320207+c.upper)) = pointBounds65989 := by
 decide +kernel
def cuts65990 : List PrefixCut := [⟨64,187293441,187293551⟩]
theorem checked65990 : checkPrefixCuts (2^48) 8653373441 10 Manual.Count131072.C065990.packed 64 cuts65990 = true := by
 decide +kernel
def cuts65991 : List PrefixCut := [⟨45,130075870,130075946⟩,
⟨64,184883618,184883723⟩]
theorem checked65991 : checkPrefixCuts (2^48) 8653504513 10 Manual.Count131072.C065991.packed 64 cuts65991 = true := by
 decide +kernel
def pointBounds65991 : List (Nat × Nat × Nat) := [(8653596672,115089660042558,115090049124596)]
theorem point_links_checked65991 : (cuts65991.take 1).map (fun c => (8653504513-1+2*2^10*c.k,115089529966688+c.lower,115089919048650+c.upper)) = pointBounds65991 := by
 decide +kernel
def cuts65992 : List PrefixCut := [⟨64,185173554,185173661⟩]
theorem checked65992 : checkPrefixCuts (2^48) 8653635585 10 Manual.Count131072.C065992.packed 64 cuts65992 = true := by
 decide +kernel
def cuts65993 : List PrefixCut := [⟨50,146855307,146855395⟩,
⟨64,188748598,188748712⟩]
theorem checked65993 : checkPrefixCuts (2^48) 8653766657 10 Manual.Count131072.C065993.packed 64 cuts65993 = true := by
 decide +kernel
def pointBounds65993 : List (Nat × Nat × Nat) := [(8653869056,115090046879167,115090435961429)]
theorem point_links_checked65993 : (cuts65993.take 1).map (fun c => (8653766657-1+2*2^10*c.k,115089900023860+c.lower,115090289106034+c.upper)) = pointBounds65993 := by
 decide +kernel
def cuts65994 : List PrefixCut := [⟨64,183606730,183606838⟩]
theorem checked65994 : checkPrefixCuts (2^48) 8653897729 10 Manual.Count131072.C065994.packed 64 cuts65994 = true := by
 decide +kernel
def cuts65995 : List PrefixCut := [⟨55,161584640,161584729⟩,
⟨64,187702088,187702194⟩]
theorem checked65995 : checkPrefixCuts (2^48) 8654028801 10 Manual.Count131072.C065995.packed 64 cuts65995 = true := by
 decide +kernel
def pointBounds65995 : List (Nat × Nat × Nat) := [(8654141440,115090433963828,115090823046313)]
theorem point_links_checked65995 : (cuts65995.take 1).map (fun c => (8654028801-1+2*2^10*c.k,115090272379188+c.lower,115090661461584+c.upper)) = pointBounds65995 := by
 decide +kernel
def cuts65996 : List PrefixCut := [⟨64,188674998,188675105⟩]
theorem checked65996 : checkPrefixCuts (2^48) 8654159873 10 Manual.Count131072.C065996.packed 64 cuts65996 = true := by
 decide +kernel
def cuts65997 : List PrefixCut := [⟨60,174068894,174069000⟩,
⟨64,185257094,185257208⟩]
theorem checked65997 : checkPrefixCuts (2^48) 8654290945 10 Manual.Count131072.C065997.packed 64 cuts65997 = true := by
 decide +kernel
def pointBounds65997 : List (Nat × Nat × Nat) := [(8654413824,115090822825168,115091211907883)]
theorem point_links_checked65997 : (cuts65997.take 1).map (fun c => (8654290945-1+2*2^10*c.k,115090648756274+c.lower,115091037838883+c.upper)) = pointBounds65997 := by
 decide +kernel
def cuts65998 : List PrefixCut := [⟨64,183628112,183628219⟩]
theorem checked65998 : checkPrefixCuts (2^48) 8654422017 10 Manual.Count131072.C065998.packed 64 cuts65998 = true := by
 decide +kernel
def cuts65999 : List PrefixCut := [⟨64,185901962,185902070⟩]
theorem checked65999 : checkPrefixCuts (2^48) 8654553089 10 Manual.Count131072.C065999.packed 64 cuts65999 = true := by
 decide +kernel
def cuts66000 : List PrefixCut := [⟨1,2829487,2829488⟩,
⟨64,185899141,185899247⟩]
theorem checked66000 : checkPrefixCuts (2^48) 8654684161 10 Manual.Count131072.C066000.packed 64 cuts66000 = true := by
 decide +kernel
def pointBounds66000 : List (Nat × Nat × Nat) := [(8654686208,115091206372929,115091595455868)]
theorem point_links_checked66000 : (cuts66000.take 1).map (fun c => (8654684161-1+2*2^10*c.k,115091203543442+c.lower,115091592626380+c.upper)) = pointBounds66000 := by
 decide +kernel
def cuts66001 : List PrefixCut := [⟨64,183587244,183587349⟩]
theorem checked66001 : checkPrefixCuts (2^48) 8654815233 10 Manual.Count131072.C066001.packed 64 cuts66001 = true := by
 decide +kernel
def cuts66002 : List PrefixCut := [⟨6,17789443,17789451⟩,
⟨64,186641516,186641621⟩]
theorem checked66002 : checkPrefixCuts (2^48) 8654946305 10 Manual.Count131072.C066002.packed 64 cuts66002 = true := by
 decide +kernel
def pointBounds66002 : List (Nat × Nat × Nat) := [(8654958592,115091590819270,115091979902427)]
theorem point_links_checked66002 : (cuts66002.take 1).map (fun c => (8654946305-1+2*2^10*c.k,115091573029827+c.lower,115091962112976+c.upper)) = pointBounds66002 := by
 decide +kernel
def cuts66003 : List PrefixCut := [⟨64,186476073,186476183⟩]
theorem checked66003 : checkPrefixCuts (2^48) 8655077377 10 Manual.Count131072.C066003.packed 64 cuts66003 = true := by
 decide +kernel
def cuts66004 : List PrefixCut := [⟨11,32813513,32813534⟩,
⟨64,186505765,186505878⟩]
theorem checked66004 : checkPrefixCuts (2^48) 8655208449 10 Manual.Count131072.C066004.packed 64 cuts66004 = true := by
 decide +kernel
def pointBounds66004 : List (Nat × Nat × Nat) := [(8655230976,115091978960929,115092368044314)]
theorem point_links_checked66004 : (cuts66004.take 1).map (fun c => (8655208449-1+2*2^10*c.k,115091946147416+c.lower,115092335230780+c.upper)) = pointBounds66004 := by
 decide +kernel
def cuts66005 : List PrefixCut := [⟨64,189722444,189722551⟩]
theorem checked66005 : checkPrefixCuts (2^48) 8655339521 10 Manual.Count131072.C066005.packed 64 cuts66005 = true := by
 decide +kernel
def cuts66006 : List PrefixCut := [⟨16,47121219,47121247⟩,
⟨64,188093577,188093688⟩]
theorem checked66006 : checkPrefixCuts (2^48) 8655470593 10 Manual.Count131072.C066006.packed 64 cuts66006 = true := by
 decide +kernel
def pointBounds66006 : List (Nat × Nat × Nat) := [(8655503360,115092369496844,115092758580456)]
theorem point_links_checked66006 : (cuts66006.take 1).map (fun c => (8655470593-1+2*2^10*c.k,115092322375625+c.lower,115092711459209+c.upper)) = pointBounds66006 := by
 decide +kernel
def cuts66007 : List PrefixCut := [⟨64,187212721,187212836⟩]
theorem checked66007 : checkPrefixCuts (2^48) 8655601665 10 Manual.Count131072.C066007.packed 64 cuts66007 = true := by
 decide +kernel
def cuts66008 : List PrefixCut := [⟨21,61265455,61265489⟩,
⟨64,185421353,185421460⟩]
theorem checked66008 : checkPrefixCuts (2^48) 8655732737 10 Manual.Count131072.C066008.packed 64 cuts66008 = true := by
 decide +kernel
def pointBounds66008 : List (Nat × Nat × Nat) := [(8655775744,115092758947378,115093148031222)]
theorem point_links_checked66008 : (cuts66008.take 1).map (fun c => (8655732737-1+2*2^10*c.k,115092697681923+c.lower,115093086765733+c.upper)) = pointBounds66008 := by
 decide +kernel
def cuts66009 : List PrefixCut := [⟨64,186524158,186524266⟩]
theorem checked66009 : checkPrefixCuts (2^48) 8655863809 10 Manual.Count131072.C066009.packed 64 cuts66009 = true := by
 decide +kernel
def cuts66010 : List PrefixCut := [⟨26,75473844,75473884⟩,
⟨64,185903505,185903611⟩]
theorem checked66010 : checkPrefixCuts (2^48) 8655994881 10 Manual.Count131072.C066010.packed 64 cuts66010 = true := by
 decide +kernel
def pointBounds66010 : List (Nat × Nat × Nat) := [(8656048128,115093145101278,115093534185343)]
theorem point_links_checked66010 : (cuts66010.take 1).map (fun c => (8655994881-1+2*2^10*c.k,115093069627434+c.lower,115093458711459+c.upper)) = pointBounds66010 := by
 decide +kernel
def cuts66011 : List PrefixCut := [⟨64,185868168,185868280⟩]
theorem checked66011 : checkPrefixCuts (2^48) 8656125953 10 Manual.Count131072.C066011.packed 64 cuts66011 = true := by
 decide +kernel
def cuts66012 : List PrefixCut := [⟨31,89421224,89421276⟩,
⟨64,185410125,185410235⟩]
theorem checked66012 : checkPrefixCuts (2^48) 8656257025 10 Manual.Count131072.C066012.packed 64 cuts66012 = true := by
 decide +kernel
def pointBounds66012 : List (Nat × Nat × Nat) := [(8656320512,115093530820331,115093919904626)]
theorem point_links_checked66012 : (cuts66012.take 1).map (fun c => (8656257025-1+2*2^10*c.k,115093441399107+c.lower,115093830483350+c.upper)) = pointBounds66012 := by
 decide +kernel
def cuts66013 : List PrefixCut := [⟨64,189211715,189211820⟩]
theorem checked66013 : checkPrefixCuts (2^48) 8656388097 10 Manual.Count131072.C066013.packed 64 cuts66013 = true := by
 decide +kernel
def cuts66014 : List PrefixCut := [⟨36,103855481,103855545⟩,
⟨64,186184879,186184989⟩]
theorem checked66014 : checkPrefixCuts (2^48) 8656519169 10 Manual.Count131072.C066014.packed 64 cuts66014 = true := by
 decide +kernel
def pointBounds66014 : List (Nat × Nat × Nat) := [(8656592896,115093919876428,115094308960950)]
theorem point_links_checked66014 : (cuts66014.take 1).map (fun c => (8656519169-1+2*2^10*c.k,115093816020947+c.lower,115094205105405+c.upper)) = pointBounds66014 := by
 decide +kernel
def cuts66015 : List PrefixCut := [⟨64,188198016,188198119⟩]
theorem checked66015 : checkPrefixCuts (2^48) 8656650241 10 Manual.Count131072.C066015.packed 64 cuts66015 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000187
