import PlattAssemblyKernel
import PlattCertificates.Count131072.C048032
import PlattCertificates.Count131072.C048033
import PlattCertificates.Count131072.C048034
import PlattCertificates.Count131072.C048035
import PlattCertificates.Count131072.C048036
import PlattCertificates.Count131072.C048037
import PlattCertificates.Count131072.C048038
import PlattCertificates.Count131072.C048039
import PlattCertificates.Count131072.C048040
import PlattCertificates.Count131072.C048041
import PlattCertificates.Count131072.C048042
import PlattCertificates.Count131072.C048043
import PlattCertificates.Count131072.C048044
import PlattCertificates.Count131072.C048045
import PlattCertificates.Count131072.C048046
import PlattCertificates.Count131072.C048047
import PlattCertificates.Count131072.C048048
import PlattCertificates.Count131072.C048049
import PlattCertificates.Count131072.C048050
import PlattCertificates.Count131072.C048051
import PlattCertificates.Count131072.C048052
import PlattCertificates.Count131072.C048053
import PlattCertificates.Count131072.C048054
import PlattCertificates.Count131072.C048055
import PlattCertificates.Count131072.C048056
import PlattCertificates.Count131072.C048057
import PlattCertificates.Count131072.C048058
import PlattCertificates.Count131072.C048059
import PlattCertificates.Count131072.C048060
import PlattCertificates.Count131072.C048061
import PlattCertificates.Count131072.C048062
import PlattCertificates.Count131072.C048063
namespace ChenEffective.PlattWindow.Assembly.Prefix.S5.B000251
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts48032 : List PrefixCut := [⟨64,260579909,260580056⟩]
theorem checked48032 : checkPrefixCuts (2^48) 6299582465 10 Manual.Count131072.C048032.packed 64 cuts48032 = true := by
 decide +kernel
def cuts48033 : List PrefixCut := [⟨25,100843679,100843737⟩,
⟨64,261512750,261512900⟩]
theorem checked48033 : checkPrefixCuts (2^48) 6299713537 10 Manual.Count131072.C048033.packed 64 cuts48033 = true := by
 decide +kernel
def pointBounds48033 : List (Nat × Nat × Nat) := [(6299764736,111157103743317,111157490580138)]
theorem point_links_checked48033 : (cuts48033.take 1).map (fun c => (6299713537-1+2*2^10*c.k,111157002899638+c.lower,111157389736401+c.upper)) = pointBounds48033 := by
 decide +kernel
def cuts48034 : List PrefixCut := [⟨58,235012791,235012929⟩,
⟨64,258826577,258826727⟩]
theorem checked48034 : checkPrefixCuts (2^48) 6299844609 10 Manual.Count131072.C048034.packed 64 cuts48034 = true := by
 decide +kernel
def pointBounds48034 : List (Nat × Nat × Nat) := [(6299963392,111157499425179,111157886262230)]
theorem point_links_checked48034 : (cuts48034.take 1).map (fun c => (6299844609-1+2*2^10*c.k,111157264412388+c.lower,111157651249301+c.upper)) = pointBounds48034 := by
 decide +kernel
def cuts48035 : List PrefixCut := [⟨64,260652988,260653135⟩]
theorem checked48035 : checkPrefixCuts (2^48) 6299975681 10 Manual.Count131072.C048035.packed 64 cuts48035 = true := by
 decide +kernel
def cuts48036 : List PrefixCut := [⟨27,108968672,108968736⟩,
⟨64,256849991,256850142⟩]
theorem checked48036 : checkPrefixCuts (2^48) 6300106753 10 Manual.Count131072.C048036.packed 64 cuts48036 = true := by
 decide +kernel
def pointBounds48036 : List (Nat × Nat × Nat) := [(6300162048,111157892860625,111158279697899)]
theorem point_links_checked48036 : (cuts48036.take 1).map (fun c => (6300106753-1+2*2^10*c.k,111157783891953+c.lower,111158170729163+c.upper)) = pointBounds48036 := by
 decide +kernel
def cuts48037 : List PrefixCut := [⟨60,242771727,242771864⟩,
⟨64,258989104,258989250⟩]
theorem checked48037 : checkPrefixCuts (2^48) 6300237825 10 Manual.Count131072.C048037.packed 64 cuts48037 = true := by
 decide +kernel
def pointBounds48037 : List (Nat × Nat × Nat) := [(6300360704,111158283513671,111158670351169)]
theorem point_links_checked48037 : (cuts48037.take 1).map (fun c => (6300237825-1+2*2^10*c.k,111158040741944+c.lower,111158427579305+c.upper)) = pointBounds48037 := by
 decide +kernel
def cuts48038 : List PrefixCut := [⟨64,260234625,260234779⟩]
theorem checked48038 : checkPrefixCuts (2^48) 6300368897 10 Manual.Count131072.C048038.packed 64 cuts48038 = true := by
 decide +kernel
def cuts48039 : List PrefixCut := [⟨29,118790287,118790356⟩,
⟨64,261212057,261212208⟩]
theorem checked48039 : checkPrefixCuts (2^48) 6300499969 10 Manual.Count131072.C048039.packed 64 cuts48039 = true := by
 decide +kernel
def pointBounds48039 : List (Nat × Nat × Nat) := [(6300559360,111158678755960,111159065593690)]
theorem point_links_checked48039 : (cuts48039.take 1).map (fun c => (6300499969-1+2*2^10*c.k,111158559965673+c.lower,111158946803334+c.upper)) = pointBounds48039 := by
 decide +kernel
def cuts48040 : List PrefixCut := [⟨62,251646556,251646702⟩,
⟨64,259553706,259553856⟩]
theorem checked48040 : checkPrefixCuts (2^48) 6300631041 10 Manual.Count131072.C048040.packed 64 cuts48040 = true := by
 decide +kernel
def pointBounds48040 : List (Nat × Nat × Nat) := [(6300758016,111159072824286,111159459662244)]
theorem point_links_checked48040 : (cuts48040.take 1).map (fun c => (6300631041-1+2*2^10*c.k,111158821177730+c.lower,111159208015542+c.upper)) = pointBounds48040 := by
 decide +kernel
def cuts48041 : List PrefixCut := [⟨64,258565498,258565644⟩]
theorem checked48041 : checkPrefixCuts (2^48) 6300762113 10 Manual.Count131072.C048041.packed 64 cuts48041 = true := by
 decide +kernel
def cuts48042 : List PrefixCut := [⟨31,125438969,125439044⟩,
⟨64,261642463,261642623⟩]
theorem checked48042 : checkPrefixCuts (2^48) 6300893185 10 Manual.Count131072.C048042.packed 64 cuts48042 = true := by
 decide +kernel
def pointBounds48042 : List (Nat × Nat × Nat) := [(6300956672,111159464735903,111159851574086)]
theorem point_links_checked48042 : (cuts48042.take 1).map (fun c => (6300893185-1+2*2^10*c.k,111159339296934+c.lower,111159726135042+c.upper)) = pointBounds48042 := by
 decide +kernel
def cuts48043 : List PrefixCut := [⟨64,258554782,258554927⟩]
theorem checked48043 : checkPrefixCuts (2^48) 6301024257 10 Manual.Count131072.C048043.packed 64 cuts48043 = true := by
 decide +kernel
def pointBounds48043 : List (Nat × Nat × Nat) := [(6301155328,111159859494179,111160246332592)]
theorem point_links_checked48043 : (cuts48043.take 1).map (fun c => (6301024257-1+2*2^10*c.k,111159600939397+c.lower,111159987777665+c.upper)) = pointBounds48043 := by
 decide +kernel
def cuts48044 : List PrefixCut := [⟨64,259710781,259710929⟩]
theorem checked48044 : checkPrefixCuts (2^48) 6301155329 10 Manual.Count131072.C048044.packed 64 cuts48044 = true := by
 decide +kernel
def cuts48045 : List PrefixCut := [⟨33,134454283,134454360⟩,
⟨64,258454675,258454824⟩]
theorem checked48045 : checkPrefixCuts (2^48) 6301286401 10 Manual.Count131072.C048045.packed 64 cuts48045 = true := by
 decide +kernel
def pointBounds48045 : List (Nat × Nat × Nat) := [(6301353984,111160253659243,111160640497881)]
theorem point_links_checked48045 : (cuts48045.take 1).map (fun c => (6301286401-1+2*2^10*c.k,111160119204960+c.lower,111160506043521+c.upper)) = pointBounds48045 := by
 decide +kernel
def cuts48046 : List PrefixCut := [⟨64,257689929,257690078⟩]
theorem checked48046 : checkPrefixCuts (2^48) 6301417473 10 Manual.Count131072.C048046.packed 64 cuts48046 = true := by
 decide +kernel
def cuts48047 : List PrefixCut := [⟨2,8174164,8174169⟩,
⟨64,258265228,258265382⟩]
theorem checked48047 : checkPrefixCuts (2^48) 6301548545 10 Manual.Count131072.C048047.packed 64 cuts48047 = true := by
 decide +kernel
def pointBounds48047 : List (Nat × Nat × Nat) := [(6301552640,111160643523728,111161030362592)]
theorem point_links_checked48047 : (cuts48047.take 1).map (fun c => (6301548545-1+2*2^10*c.k,111160635349564+c.lower,111161022188423+c.upper)) = pointBounds48047 := by
 decide +kernel
def cuts48048 : List PrefixCut := [⟨35,139805807,139805890⟩,
⟨64,257187870,257188018⟩]
theorem checked48048 : checkPrefixCuts (2^48) 6301679617 10 Manual.Count131072.C048048.packed 64 cuts48048 = true := by
 decide +kernel
def pointBounds48048 : List (Nat × Nat × Nat) := [(6301751296,111161033420599,111161420259695)]
theorem point_links_checked48048 : (cuts48048.take 1).map (fun c => (6301679617-1+2*2^10*c.k,111160893614792+c.lower,111161280453805+c.upper)) = pointBounds48048 := by
 decide +kernel
def cuts48049 : List PrefixCut := [⟨64,259728471,259728615⟩]
theorem checked48049 : checkPrefixCuts (2^48) 6301810689 10 Manual.Count131072.C048049.packed 64 cuts48049 = true := by
 decide +kernel
def cuts48050 : List PrefixCut := [⟨4,15543336,15543345⟩,
⟨64,256283892,256284044⟩]
theorem checked48050 : checkPrefixCuts (2^48) 6301941761 10 Manual.Count131072.C048050.packed 64 cuts48050 = true := by
 decide +kernel
def pointBounds48050 : List (Nat × Nat × Nat) := [(6301949952,111161426074469,111161812913783)]
theorem point_links_checked48050 : (cuts48050.take 1).map (fun c => (6301941761-1+2*2^10*c.k,111161410531133+c.lower,111161797370438+c.upper)) = pointBounds48050 := by
 decide +kernel
def cuts48051 : List PrefixCut := [⟨37,148863746,148863830⟩,
⟨64,257171829,257171970⟩]
theorem checked48051 : checkPrefixCuts (2^48) 6302072833 10 Manual.Count131072.C048051.packed 64 cuts48051 = true := by
 decide +kernel
def pointBounds48051 : List (Nat × Nat × Nat) := [(6302148608,111161815678771,111162202518312)]
theorem point_links_checked48051 : (cuts48051.take 1).map (fun c => (6302072833-1+2*2^10*c.k,111161666815025+c.lower,111162053654482+c.upper)) = pointBounds48051 := by
 decide +kernel
def cuts48052 : List PrefixCut := [⟨64,257970387,257970535⟩]
theorem checked48052 : checkPrefixCuts (2^48) 6302203905 10 Manual.Count131072.C048052.packed 64 cuts48052 = true := by
 decide +kernel
def cuts48053 : List PrefixCut := [⟨6,24296106,24296121⟩,
⟨64,260108792,260108940⟩]
theorem checked48053 : checkPrefixCuts (2^48) 6302334977 10 Manual.Count131072.C048053.packed 64 cuts48053 = true := by
 decide +kernel
def pointBounds48053 : List (Nat × Nat × Nat) := [(6302347264,111162206253347,111162593093108)]
theorem point_links_checked48053 : (cuts48053.take 1).map (fun c => (6302334977-1+2*2^10*c.k,111162181957241+c.lower,111162568796987+c.upper)) = pointBounds48053 := by
 decide +kernel
def cuts48054 : List PrefixCut := [⟨39,158992415,158992503⟩,
⟨64,258540278,258540423⟩]
theorem checked48054 : checkPrefixCuts (2^48) 6302466049 10 Manual.Count131072.C048054.packed 64 cuts48054 = true := by
 decide +kernel
def pointBounds48054 : List (Nat × Nat × Nat) := [(6302545920,111162601058448,111162987898430)]
theorem point_links_checked48054 : (cuts48054.take 1).map (fun c => (6302466049-1+2*2^10*c.k,111162442066033+c.lower,111162828905927+c.upper)) = pointBounds48054 := by
 decide +kernel
def cuts48055 : List PrefixCut := [⟨64,258132959,258133106⟩]
theorem checked48055 : checkPrefixCuts (2^48) 6302597121 10 Manual.Count131072.C048055.packed 64 cuts48055 = true := by
 decide +kernel
def cuts48056 : List PrefixCut := [⟨8,32645843,32645863⟩,
⟨64,259333364,259333518⟩]
theorem checked48056 : checkPrefixCuts (2^48) 6302728193 10 Manual.Count131072.C048056.packed 64 cuts48056 = true := by
 decide +kernel
def pointBounds48056 : List (Nat × Nat × Nat) := [(6302744576,111162991385113,111163378225319)]
theorem point_links_checked48056 : (cuts48056.take 1).map (fun c => (6302728193-1+2*2^10*c.k,111162958739270+c.lower,111163345579456+c.upper)) = pointBounds48056 := by
 decide +kernel
def cuts48057 : List PrefixCut := [⟨41,168226639,168226733⟩,
⟨64,261203611,261203757⟩]
theorem checked48057 : checkPrefixCuts (2^48) 6302859265 10 Manual.Count131072.C048057.packed 64 cuts48057 = true := by
 decide +kernel
def pointBounds48057 : List (Nat × Nat × Nat) := [(6302943232,111163386299273,111163773139707)]
theorem point_links_checked48057 : (cuts48057.take 1).map (fun c => (6302859265-1+2*2^10*c.k,111163218072634+c.lower,111163604912974+c.upper)) = pointBounds48057 := by
 decide +kernel
def cuts48058 : List PrefixCut := [⟨64,258920652,258920795⟩]
theorem checked48058 : checkPrefixCuts (2^48) 6302990337 10 Manual.Count131072.C048058.packed 64 cuts48058 = true := by
 decide +kernel
def cuts48059 : List PrefixCut := [⟨10,41262471,41262495⟩,
⟨64,254449664,254449820⟩]
theorem checked48059 : checkPrefixCuts (2^48) 6303121409 10 Manual.Count131072.C048059.packed 64 cuts48059 = true := by
 decide +kernel
def pointBounds48059 : List (Nat × Nat × Nat) := [(6303141888,111163779459368,111164166300021)]
theorem point_links_checked48059 : (cuts48059.take 1).map (fun c => (6303121409-1+2*2^10*c.k,111163738196897+c.lower,111164125037526+c.upper)) = pointBounds48059 := by
 decide +kernel
def cuts48060 : List PrefixCut := [⟨43,175941454,175941554⟩,
⟨64,261276632,261276778⟩]
theorem checked48060 : checkPrefixCuts (2^48) 6303252481 10 Manual.Count131072.C048060.packed 64 cuts48060 = true := by
 decide +kernel
def pointBounds48060 : List (Nat × Nat × Nat) := [(6303340544,111164168588015,111164555428900)]
theorem point_links_checked48060 : (cuts48060.take 1).map (fun c => (6303252481-1+2*2^10*c.k,111163992646561+c.lower,111164379487346+c.upper)) = pointBounds48060 := by
 decide +kernel
def cuts48061 : List PrefixCut := [⟨64,259708268,259708414⟩]
theorem checked48061 : checkPrefixCuts (2^48) 6303383553 10 Manual.Count131072.C048061.packed 64 cuts48061 = true := by
 decide +kernel
def cuts48062 : List PrefixCut := [⟨12,48181188,48181216⟩,
⟨64,260417333,260417477⟩]
theorem checked48062 : checkPrefixCuts (2^48) 6303514625 10 Manual.Count131072.C048062.packed 64 cuts48062 = true := by
 decide +kernel
def pointBounds48062 : List (Nat × Nat × Nat) := [(6303539200,111164561812649,111164948653754)]
theorem point_links_checked48062 : (cuts48062.take 1).map (fun c => (6303514625-1+2*2^10*c.k,111164513631461+c.lower,111164900472538+c.upper)) = pointBounds48062 := by
 decide +kernel
def cuts48063 : List PrefixCut := [⟨45,184726941,184727044⟩,
⟨64,265457623,265457769⟩]
theorem checked48063 : checkPrefixCuts (2^48) 6303645697 10 Manual.Count131072.C048063.packed 64 cuts48063 = true := by
 decide +kernel
def pointBounds48063 : List (Nat × Nat × Nat) := [(6303737856,111164958775735,111165345617059)]
theorem point_links_checked48063 : (cuts48063.take 1).map (fun c => (6303645697-1+2*2^10*c.k,111164774048794+c.lower,111165160890015+c.upper)) = pointBounds48063 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S5.B000251
