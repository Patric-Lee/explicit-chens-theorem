import PlattAssemblyKernel
import PlattCertificates.Count131072.C037008
import PlattCertificates.Count131072.C037009
import PlattCertificates.Count131072.C037010
import PlattCertificates.Count131072.C037011
import PlattCertificates.Count131072.C037012
import PlattCertificates.Count131072.C037013
import PlattCertificates.Count131072.C037014
import PlattCertificates.Count131072.C037015
import PlattCertificates.Count131072.C037016
import PlattCertificates.Count131072.C037017
import PlattCertificates.Count131072.C037018
import PlattCertificates.Count131072.C037019
import PlattCertificates.Count131072.C037020
import PlattCertificates.Count131072.C037021
import PlattCertificates.Count131072.C037022
import PlattCertificates.Count131072.C037023
import PlattCertificates.Count131072.C037024
import PlattCertificates.Count131072.C037025
import PlattCertificates.Count131072.C037026
import PlattCertificates.Count131072.C037027
import PlattCertificates.Count131072.C037028
import PlattCertificates.Count131072.C037029
import PlattCertificates.Count131072.C037030
import PlattCertificates.Count131072.C037031
import PlattCertificates.Count131072.C037032
import PlattCertificates.Count131072.C037033
import PlattCertificates.Count131072.C037034
import PlattCertificates.Count131072.C037035
import PlattCertificates.Count131072.C037036
import PlattCertificates.Count131072.C037037
import PlattCertificates.Count131072.C037038
import PlattCertificates.Count131072.C037039
namespace ChenEffective.PlattWindow.Assembly.Prefix.S4.B000219
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts37008 : List PrefixCut := [⟨23,122860160,122860238⟩,
⟨64,336282593,336282801⟩]
theorem checked37008 : checkPrefixCuts (2^48) 4854644737 10 Manual.Count131072.C037008.packed 64 cuts37008 = true := by
 decide +kernel
def pointBounds37008 : List (Nat × Nat × Nat) := [(4854691840,107887667127583,107888052044395)]
theorem point_links_checked37008 : (cuts37008.take 1).map (fun c => (4854644737-1+2*2^10*c.k,107887544267423+c.lower,107887929184157+c.upper)) = pointBounds37008 := by
 decide +kernel
def cuts37009 : List PrefixCut := [⟨34,181646813,181646921⟩,
⟨64,338244776,338244977⟩]
theorem checked37009 : checkPrefixCuts (2^48) 4854775809 10 Manual.Count131072.C037009.packed 64 cuts37009 = true := by
 decide +kernel
def pointBounds37009 : List (Nat × Nat × Nat) := [(4854845440,107888062196829,107888447113879)]
theorem point_links_checked37009 : (cuts37009.take 1).map (fun c => (4854775809-1+2*2^10*c.k,107887880550016+c.lower,107888265466958+c.upper)) = pointBounds37009 := by
 decide +kernel
def cuts37010 : List PrefixCut := [⟨45,237299258,237299405⟩,
⟨64,339627027,339627235⟩]
theorem checked37010 : checkPrefixCuts (2^48) 4854906881 10 Manual.Count131072.C037010.packed 64 cuts37010 = true := by
 decide +kernel
def pointBounds37010 : List (Nat × Nat × Nat) := [(4854999040,107888456094050,107888841011340)]
theorem point_links_checked37010 : (cuts37010.take 1).map (fun c => (4854906881-1+2*2^10*c.k,107888218794792+c.lower,107888603711935+c.upper)) = pointBounds37010 := by
 decide +kernel
def cuts37011 : List PrefixCut := [⟨56,297644410,297644589⟩,
⟨64,341588984,341589188⟩]
theorem checked37011 : checkPrefixCuts (2^48) 4855037953 10 Manual.Count131072.C037011.packed 64 cuts37011 = true := by
 decide +kernel
def pointBounds37011 : List (Nat × Nat × Nat) := [(4855152640,107888856066229,107889240983759)]
theorem point_links_checked37011 : (cuts37011.take 1).map (fun c => (4855037953-1+2*2^10*c.k,107888558421819+c.lower,107888943339170+c.upper)) = pointBounds37011 := by
 decide +kernel
def cuts37012 : List PrefixCut := [⟨64,337869486,337869689⟩]
theorem checked37012 : checkPrefixCuts (2^48) 4855169025 10 Manual.Count131072.C037012.packed 64 cuts37012 = true := by
 decide +kernel
def cuts37013 : List PrefixCut := [⟨3,15652620,15652630⟩,
⟨64,340063329,340063535⟩]
theorem checked37013 : checkPrefixCuts (2^48) 4855300097 10 Manual.Count131072.C037013.packed 64 cuts37013 = true := by
 decide +kernel
def pointBounds37013 : List (Nat × Nat × Nat) := [(4855306240,107889253532909,107889638450677)]
theorem point_links_checked37013 : (cuts37013.take 1).map (fun c => (4855300097-1+2*2^10*c.k,107889237880289+c.lower,107889622798047+c.upper)) = pointBounds37013 := by
 decide +kernel
def cuts37014 : List PrefixCut := [⟨14,74376756,74376800⟩,
⟨64,344865650,344865853⟩]
theorem checked37014 : checkPrefixCuts (2^48) 4855431169 10 Manual.Count131072.C037014.packed 64 cuts37014 = true := by
 decide +kernel
def pointBounds37014 : List (Nat × Nat × Nat) := [(4855459840,107889652320374,107890037238382)]
theorem point_links_checked37014 : (cuts37014.take 1).map (fun c => (4855431169-1+2*2^10*c.k,107889577943618+c.lower,107889962861582+c.upper)) = pointBounds37014 := by
 decide +kernel
def cuts37015 : List PrefixCut := [⟨25,130141004,130141084⟩,
⟨64,337668201,337668407⟩]
theorem checked37015 : checkPrefixCuts (2^48) 4855562241 10 Manual.Count131072.C037015.packed 64 cuts37015 = true := by
 decide +kernel
def pointBounds37015 : List (Nat × Nat × Nat) := [(4855613440,107890052950272,107890437868519)]
theorem point_links_checked37015 : (cuts37015.take 1).map (fun c => (4855562241-1+2*2^10*c.k,107889922809268+c.lower,107890307727435+c.upper)) = pointBounds37015 := by
 decide +kernel
def cuts37016 : List PrefixCut := [⟨36,191061125,191061239⟩,
⟨64,342528344,342528553⟩]
theorem checked37016 : checkPrefixCuts (2^48) 4855693313 10 Manual.Count131072.C037016.packed 64 cuts37016 = true := by
 decide +kernel
def pointBounds37016 : List (Nat × Nat × Nat) := [(4855767040,107890451538594,107890836457081)]
theorem point_links_checked37016 : (cuts37016.take 1).map (fun c => (4855693313-1+2*2^10*c.k,107890260477469+c.lower,107890645395842+c.upper)) = pointBounds37016 := by
 decide +kernel
def cuts37017 : List PrefixCut := [⟨47,250006795,250006948⟩,
⟨64,339794727,339794936⟩]
theorem checked37017 : checkPrefixCuts (2^48) 4855824385 10 Manual.Count131072.C037017.packed 64 cuts37017 = true := by
 decide +kernel
def pointBounds37017 : List (Nat × Nat × Nat) := [(4855920640,107890853012608,107891237931343)]
theorem point_links_checked37017 : (cuts37017.take 1).map (fun c => (4855824385-1+2*2^10*c.k,107890603005813+c.lower,107890987924395+c.upper)) = pointBounds37017 := by
 decide +kernel
def cuts37018 : List PrefixCut := [⟨58,311035762,311035953⟩,
⟨64,343437298,343437507⟩]
theorem checked37018 : checkPrefixCuts (2^48) 4855955457 10 Manual.Count131072.C037018.packed 64 cuts37018 = true := by
 decide +kernel
def pointBounds37018 : List (Nat × Nat × Nat) := [(4856074240,107891253836302,107891638755284)]
theorem point_links_checked37018 : (cuts37018.take 1).map (fun c => (4855955457-1+2*2^10*c.k,107890942800540+c.lower,107891327719331+c.upper)) = pointBounds37018 := by
 decide +kernel
def cuts37019 : List PrefixCut := [⟨64,339312688,339312896⟩]
theorem checked37019 : checkPrefixCuts (2^48) 4856086529 10 Manual.Count131072.C037019.packed 64 cuts37019 = true := by
 decide +kernel
def cuts37020 : List PrefixCut := [⟨5,27705688,27705706⟩,
⟨64,344751870,344752081⟩]
theorem checked37020 : checkPrefixCuts (2^48) 4856217601 10 Manual.Count131072.C037020.packed 64 cuts37020 = true := by
 decide +kernel
def pointBounds37020 : List (Nat × Nat × Nat) := [(4856227840,107891653256214,107892038175440)]
theorem point_links_checked37020 : (cuts37020.take 1).map (fun c => (4856217601-1+2*2^10*c.k,107891625550526+c.lower,107892010469734+c.upper)) = pointBounds37020 := by
 decide +kernel
def cuts37021 : List PrefixCut := [⟨16,84447706,84447757⟩,
⟨64,340917220,340917429⟩]
theorem checked37021 : checkPrefixCuts (2^48) 4856348673 10 Manual.Count131072.C037021.packed 64 cuts37021 = true := by
 decide +kernel
def pointBounds37021 : List (Nat × Nat × Nat) := [(4856381440,107892054750102,107892439669572)]
theorem point_links_checked37021 : (cuts37021.take 1).map (fun c => (4856348673-1+2*2^10*c.k,107891970302396+c.lower,107892355221815+c.upper)) = pointBounds37021 := by
 decide +kernel
def cuts37022 : List PrefixCut := [⟨27,141128437,141128525⟩,
⟨64,339806793,339807006⟩]
theorem checked37022 : checkPrefixCuts (2^48) 4856479745 10 Manual.Count131072.C037022.packed 64 cuts37022 = true := by
 decide +kernel
def pointBounds37022 : List (Nat × Nat × Nat) := [(4856535040,107892452348053,107892837267769)]
theorem point_links_checked37022 : (cuts37022.take 1).map (fun c => (4856479745-1+2*2^10*c.k,107892311219616+c.lower,107892696139244+c.upper)) = pointBounds37022 := by
 decide +kernel
def cuts37023 : List PrefixCut := [⟨38,203601518,203601644⟩,
⟨64,339449955,339450168⟩]
theorem checked37023 : checkPrefixCuts (2^48) 4856610817 10 Manual.Count131072.C037023.packed 64 cuts37023 = true := by
 decide +kernel
def pointBounds37023 : List (Nat × Nat × Nat) := [(4856688640,107892854627927,107893239547894)]
theorem point_links_checked37023 : (cuts37023.take 1).map (fun c => (4856610817-1+2*2^10*c.k,107892651026409+c.lower,107893035946250+c.upper)) = pointBounds37023 := by
 decide +kernel
def cuts37024 : List PrefixCut := [⟨49,261260695,261260853⟩,
⟨64,341758964,341759173⟩]
theorem checked37024 : checkPrefixCuts (2^48) 4856741889 10 Manual.Count131072.C037024.packed 64 cuts37024 = true := by
 decide +kernel
def pointBounds37024 : List (Nat × Nat × Nat) := [(4856842240,107893251737059,107893636657271)]
theorem point_links_checked37024 : (cuts37024.take 1).map (fun c => (4856741889-1+2*2^10*c.k,107892990476364+c.lower,107893375396418+c.upper)) = pointBounds37024 := by
 decide +kernel
def cuts37025 : List PrefixCut := [⟨60,322509553,322509747⟩,
⟨64,343836043,343836250⟩]
theorem checked37025 : checkPrefixCuts (2^48) 4856872961 10 Manual.Count131072.C037025.packed 64 cuts37025 = true := by
 decide +kernel
def pointBounds37025 : List (Nat × Nat × Nat) := [(4856995840,107893654744881,107894039665338)]
theorem point_links_checked37025 : (cuts37025.take 1).map (fun c => (4856872961-1+2*2^10*c.k,107893332235328+c.lower,107893717155591+c.upper)) = pointBounds37025 := by
 decide +kernel
def cuts37026 : List PrefixCut := [⟨64,339886082,339886296⟩]
theorem checked37026 : checkPrefixCuts (2^48) 4857004033 10 Manual.Count131072.C037026.packed 64 cuts37026 = true := by
 decide +kernel
def cuts37027 : List PrefixCut := [⟨7,39174687,39174710⟩,
⟨64,340340507,340340716⟩]
theorem checked37027 : checkPrefixCuts (2^48) 4857135105 10 Manual.Count131072.C037027.packed 64 cuts37027 = true := by
 decide +kernel
def pointBounds37027 : List (Nat × Nat × Nat) := [(4857149440,107894055132140,107894440052847)]
theorem point_links_checked37027 : (cuts37027.take 1).map (fun c => (4857135105-1+2*2^10*c.k,107894015957453+c.lower,107894400878137+c.upper)) = pointBounds37027 := by
 decide +kernel
def cuts37028 : List PrefixCut := [⟨18,94109208,94109265⟩,
⟨64,339404099,339404302⟩]
theorem checked37028 : checkPrefixCuts (2^48) 4857266177 10 Manual.Count131072.C037028.packed 64 cuts37028 = true := by
 decide +kernel
def pointBounds37028 : List (Nat × Nat × Nat) := [(4857303040,107894450407168,107894835328118)]
theorem point_links_checked37028 : (cuts37028.take 1).map (fun c => (4857266177-1+2*2^10*c.k,107894356297960+c.lower,107894741218853+c.upper)) = pointBounds37028 := by
 decide +kernel
def cuts37029 : List PrefixCut := [⟨29,156747507,156747599⟩,
⟨64,339510900,339511105⟩]
theorem checked37029 : checkPrefixCuts (2^48) 4857397249 10 Manual.Count131072.C037029.packed 64 cuts37029 = true := by
 decide +kernel
def pointBounds37029 : List (Nat × Nat × Nat) := [(4857456640,107894852449566,107895237370754)]
theorem point_links_checked37029 : (cuts37029.take 1).map (fun c => (4857397249-1+2*2^10*c.k,107894695702059+c.lower,107895080623155+c.upper)) = pointBounds37029 := by
 decide +kernel
def cuts37030 : List PrefixCut := [⟨40,210632337,210632468⟩,
⟨64,339501671,339501879⟩]
theorem checked37030 : checkPrefixCuts (2^48) 4857528321 10 Manual.Count131072.C037030.packed 64 cuts37030 = true := by
 decide +kernel
def pointBounds37030 : List (Nat × Nat × Nat) := [(4857610240,107895245845296,107895630766728)]
theorem point_links_checked37030 : (cuts37030.take 1).map (fun c => (4857528321-1+2*2^10*c.k,107895035212959+c.lower,107895420134260+c.upper)) = pointBounds37030 := by
 decide +kernel
def cuts37031 : List PrefixCut := [⟨51,270250478,270250643⟩,
⟨64,341114943,341115151⟩]
theorem checked37031 : checkPrefixCuts (2^48) 4857659393 10 Manual.Count131072.C037031.packed 64 cuts37031 = true := by
 decide +kernel
def pointBounds37031 : List (Nat × Nat × Nat) := [(4857763840,107895644965108,107896029886782)]
theorem point_links_checked37031 : (cuts37031.take 1).map (fun c => (4857659393-1+2*2^10*c.k,107895374714630+c.lower,107895759636139+c.upper)) = pointBounds37031 := by
 decide +kernel
def cuts37032 : List PrefixCut := [⟨62,331255733,331255935⟩,
⟨64,340700189,340700397⟩]
theorem checked37032 : checkPrefixCuts (2^48) 4857790465 10 Manual.Count131072.C037032.packed 64 cuts37032 = true := by
 decide +kernel
def pointBounds37032 : List (Nat × Nat × Nat) := [(4857917440,107896047085306,107896432007225)]
theorem point_links_checked37032 : (cuts37032.take 1).map (fun c => (4857790465-1+2*2^10*c.k,107895715829573+c.lower,107896100751290+c.upper)) = pointBounds37032 := by
 decide +kernel
def cuts37033 : List PrefixCut := [⟨64,337098655,337098861⟩]
theorem checked37033 : checkPrefixCuts (2^48) 4857921537 10 Manual.Count131072.C037033.packed 64 cuts37033 = true := by
 decide +kernel
def cuts37034 : List PrefixCut := [⟨9,48959088,48959119⟩,
⟨64,336046697,336046904⟩]
theorem checked37034 : checkPrefixCuts (2^48) 4858052609 10 Manual.Count131072.C037034.packed 64 cuts37034 = true := by
 decide +kernel
def pointBounds37034 : List (Nat × Nat × Nat) := [(4858071040,107896442587505,107896827509667)]
theorem point_links_checked37034 : (cuts37034.take 1).map (fun c => (4858052609-1+2*2^10*c.k,107896393628417+c.lower,107896778550548+c.upper)) = pointBounds37034 := by
 decide +kernel
def cuts37035 : List PrefixCut := [⟨20,103245610,103245673⟩,
⟨64,335979620,335979822⟩]
theorem checked37035 : checkPrefixCuts (2^48) 4858183681 10 Manual.Count131072.C037035.packed 64 cuts37035 = true := by
 decide +kernel
def pointBounds37035 : List (Nat × Nat × Nat) := [(4858224640,107896832920724,107897217843125)]
theorem point_links_checked37035 : (cuts37035.take 1).map (fun c => (4858183681-1+2*2^10*c.k,107896729675114+c.lower,107897114597452+c.upper)) = pointBounds37035 := by
 decide +kernel
def cuts37036 : List PrefixCut := [⟨31,168710658,168710760⟩,
⟨64,347094282,347094491⟩]
theorem checked37036 : checkPrefixCuts (2^48) 4858314753 10 Manual.Count131072.C037036.packed 64 cuts37036 = true := by
 decide +kernel
def pointBounds37036 : List (Nat × Nat × Nat) := [(4858378240,107897234365392,107897619288034)]
theorem point_links_checked37036 : (cuts37036.take 1).map (fun c => (4858314753-1+2*2^10*c.k,107897065654734+c.lower,107897450577274+c.upper)) = pointBounds37036 := by
 decide +kernel
def cuts37037 : List PrefixCut := [⟨42,223222239,223222377⟩,
⟨64,340016937,340017145⟩]
theorem checked37037 : checkPrefixCuts (2^48) 4858445825 10 Manual.Count131072.C037037.packed 64 cuts37037 = true := by
 decide +kernel
def pointBounds37037 : List (Nat × Nat × Nat) := [(4858531840,107897635971255,107898020894142)]
theorem point_links_checked37037 : (cuts37037.take 1).map (fun c => (4858445825-1+2*2^10*c.k,107897412749016+c.lower,107897797671765+c.upper)) = pointBounds37037 := by
 decide +kernel
def cuts37038 : List PrefixCut := [⟨53,283755658,283755833⟩,
⟨64,341398177,341398389⟩]
theorem checked37038 : checkPrefixCuts (2^48) 4858576897 10 Manual.Count131072.C037038.packed 64 cuts37038 = true := by
 decide +kernel
def pointBounds37038 : List (Nat × Nat × Nat) := [(4858685440,107898036521611,107898421444743)]
theorem point_links_checked37038 : (cuts37038.take 1).map (fun c => (4858576897-1+2*2^10*c.k,107897752765953+c.lower,107898137688910+c.upper)) = pointBounds37038 := by
 decide +kernel
def cuts37039 : List PrefixCut := [⟨64,336928242,336928448⟩]
theorem checked37039 : checkPrefixCuts (2^48) 4858707969 10 Manual.Count131072.C037039.packed 64 cuts37039 = true := by
 decide +kernel
def pointBounds37039 : List (Nat × Nat × Nat) := [(4858839040,107898431092372,107898816015747)]
theorem point_links_checked37039 : (cuts37039.take 1).map (fun c => (4858707969-1+2*2^10*c.k,107898094164130+c.lower,107898479087299+c.upper)) = pointBounds37039 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S4.B000219
