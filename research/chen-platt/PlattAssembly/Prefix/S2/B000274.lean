import PlattAssemblyKernel
import PlattCertificates.Count131072.C018768
import PlattCertificates.Count131072.C018769
import PlattCertificates.Count131072.C018770
import PlattCertificates.Count131072.C018771
import PlattCertificates.Count131072.C018772
import PlattCertificates.Count131072.C018773
import PlattCertificates.Count131072.C018774
import PlattCertificates.Count131072.C018775
import PlattCertificates.Count131072.C018776
import PlattCertificates.Count131072.C018777
import PlattCertificates.Count131072.C018778
import PlattCertificates.Count131072.C018779
import PlattCertificates.Count131072.C018780
import PlattCertificates.Count131072.C018781
import PlattCertificates.Count131072.C018782
import PlattCertificates.Count131072.C018783
import PlattCertificates.Count131072.C018784
import PlattCertificates.Count131072.C018785
import PlattCertificates.Count131072.C018786
import PlattCertificates.Count131072.C018787
import PlattCertificates.Count131072.C018788
import PlattCertificates.Count131072.C018789
import PlattCertificates.Count131072.C018790
import PlattCertificates.Count131072.C018791
import PlattCertificates.Count131072.C018792
import PlattCertificates.Count131072.C018793
import PlattCertificates.Count131072.C018794
import PlattCertificates.Count131072.C018795
import PlattCertificates.Count131072.C018796
import PlattCertificates.Count131072.C018797
import PlattCertificates.Count131072.C018798
import PlattCertificates.Count131072.C018799
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000274
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts18768 : List PrefixCut := [⟨54,293250746,293250920⟩,
⟨128,691362077,691362497⟩]
theorem checked18768 : checkPrefixCuts (2^48) 2463891457 9 Manual.Count131072.C018768.packed 128 cuts18768 = true := by
 decide +kernel
def pointBounds18768 : List (Nat × Nat × Nat) := [(2463946752,99195934585789,99196314465423)]
theorem point_links_checked18768 : (cuts18768.take 1).map (fun c => (2463891457-1+2*2^9*c.k,99195641335043+c.lower,99196021214503+c.upper)) = pointBounds18768 := by
 decide +kernel
def cuts18769 : List PrefixCut := [⟨2,11194918,11194924⟩,
⟨78,417175376,417175630⟩,
⟨128,684128569,684128989⟩]
theorem checked18769 : checkPrefixCuts (2^48) 2464022529 9 Manual.Count131072.C018769.packed 128 cuts18769 = true := by
 decide +kernel
def pointBounds18769 : List (Nat × Nat × Nat) := [(2464024576,99196343892038,99196723771924),(2464102400,99196749872496,99197129752630)]
theorem point_links_checked18769 : (cuts18769.take 2).map (fun c => (2464022529-1+2*2^9*c.k,99196332697120+c.lower,99196712577000+c.upper)) = pointBounds18769 := by
 decide +kernel
def cuts18770 : List PrefixCut := [⟨26,140156774,140156860⟩,
⟨102,553422023,553422357⟩,
⟨128,692887522,692887944⟩]
theorem checked18770 : checkPrefixCuts (2^48) 2464153601 9 Manual.Count131072.C018770.packed 128 cuts18770 = true := by
 decide +kernel
def pointBounds18770 : List (Nat × Nat × Nat) := [(2464180224,99197156982463,99197536862849),(2464258048,99197570247712,99197950128346)]
theorem point_links_checked18770 : (cuts18770.take 2).map (fun c => (2464153601-1+2*2^9*c.k,99197016825689+c.lower,99197396705989+c.upper)) = pointBounds18770 := by
 decide +kernel
def cuts18771 : List PrefixCut := [⟨50,273558257,273558420⟩,
⟨126,680172813,680173216⟩,
⟨128,690109580,690109990⟩]
theorem checked18771 : checkPrefixCuts (2^48) 2464284673 9 Manual.Count131072.C018771.packed 128 cuts18771 = true := by
 decide +kernel
def pointBounds18771 : List (Nat × Nat × Nat) := [(2464335872,99197983271468,99198363152353),(2464413696,99198389886024,99198769767149)]
theorem point_links_checked18771 : (cuts18771.take 2).map (fun c => (2464284673-1+2*2^9*c.k,99197709713211+c.lower,99198089593933+c.upper)) = pointBounds18771 := by
 decide +kernel
def cuts18772 : List PrefixCut := [⟨74,405802051,405802292⟩,
⟨128,698296161,698296578⟩]
theorem checked18772 : checkPrefixCuts (2^48) 2464415745 9 Manual.Count131072.C018772.packed 128 cuts18772 = true := by
 decide +kernel
def pointBounds18772 : List (Nat × Nat × Nat) := [(2464491520,99198805624842,99199185506215)]
theorem point_links_checked18772 : (cuts18772.take 1).map (fun c => (2464415745-1+2*2^9*c.k,99198399822791+c.lower,99198779703923+c.upper)) = pointBounds18772 := by
 decide +kernel
def cuts18773 : List PrefixCut := [⟨22,119576899,119576967⟩,
⟨98,524668180,524668498⟩,
⟨128,693576226,693576642⟩]
theorem checked18773 : checkPrefixCuts (2^48) 2464546817 9 Manual.Count131072.C018773.packed 128 cuts18773 = true := by
 decide +kernel
def pointBounds18773 : List (Nat × Nat × Nat) := [(2464569344,99199217695851,99199597577468),(2464647168,99199622787132,99200002668999)]
theorem point_links_checked18773 : (cuts18773.take 2).map (fun c => (2464546817-1+2*2^9*c.k,99199098118952+c.lower,99199478000501+c.upper)) = pointBounds18773 := by
 decide +kernel
def cuts18774 : List PrefixCut := [⟨46,246334620,246334764⟩,
⟨122,653455995,653456376⟩,
⟨128,685888111,685888510⟩]
theorem checked18774 : checkPrefixCuts (2^48) 2464677889 9 Manual.Count131072.C018774.packed 128 cuts18774 = true := by
 decide +kernel
def pointBounds18774 : List (Nat × Nat × Nat) := [(2464724992,99200038029798,99200417911907),(2464802816,99200445151173,99200825033519)]
theorem point_links_checked18774 : (cuts18774.take 2).map (fun c => (2464677889-1+2*2^9*c.k,99199791695178+c.lower,99200171577143+c.upper)) = pointBounds18774 := by
 decide +kernel
def cuts18775 : List PrefixCut := [⟨70,380500450,380500678⟩,
⟨128,696814355,696814778⟩]
theorem checked18775 : checkPrefixCuts (2^48) 2464808961 9 Manual.Count131072.C018775.packed 128 cuts18775 = true := by
 decide +kernel
def pointBounds18775 : List (Nat × Nat × Nat) := [(2464880640,99200858083739,99201237966331)]
theorem point_links_checked18775 : (cuts18775.take 1).map (fun c => (2464808961-1+2*2^9*c.k,99200477583289+c.lower,99200857465653+c.upper)) = pointBounds18775 := by
 decide +kernel
def cuts18776 : List PrefixCut := [⟨18,92723052,92723109⟩,
⟨94,504259213,504259518⟩,
⟨128,683759804,683760219⟩]
theorem checked18776 : checkPrefixCuts (2^48) 2464940033 9 Manual.Count131072.C018776.packed 128 cuts18776 = true := by
 decide +kernel
def pointBounds18776 : List (Nat × Nat × Nat) := [(2464958464,99201267120696,99201647003540),(2465036288,99201678656857,99202058539949)]
theorem point_links_checked18776 : (cuts18776.take 2).map (fun c => (2464940033-1+2*2^9*c.k,99201174397644+c.lower,99201554280431+c.upper)) = pointBounds18776 := by
 decide +kernel
def cuts18777 : List PrefixCut := [⟨42,230081380,230081517⟩,
⟨118,649470080,649470468⟩,
⟨128,704390405,704390827⟩]
theorem checked18777 : checkPrefixCuts (2^48) 2465071105 9 Manual.Count131072.C018777.packed 128 cuts18777 = true := by
 decide +kernel
def pointBounds18777 : List (Nat × Nat × Nat) := [(2465114112,99202088238828,99202468122167),(2465191936,99202507627528,99202887511118)]
theorem point_links_checked18777 : (cuts18777.take 2).map (fun c => (2465071105-1+2*2^9*c.k,99201858157448+c.lower,99202238040650+c.upper)) = pointBounds18777 := by
 decide +kernel
def cuts18778 : List PrefixCut := [⟨66,355206702,355206913⟩,
⟨128,689624222,689624633⟩]
theorem checked18778 : checkPrefixCuts (2^48) 2465202177 9 Manual.Count131072.C018778.packed 128 cuts18778 = true := by
 decide +kernel
def pointBounds18778 : List (Nat × Nat × Nat) := [(2465269760,99202917754555,99203297638390)]
theorem point_links_checked18778 : (cuts18778.take 1).map (fun c => (2465202177-1+2*2^9*c.k,99202562547853+c.lower,99202942431477+c.upper)) = pointBounds18778 := by
 decide +kernel
def cuts18779 : List PrefixCut := [⟨14,74098169,74098215⟩,
⟨90,488994473,488994770⟩,
⟨128,697693577,697693995⟩]
theorem checked18779 : checkPrefixCuts (2^48) 2465333249 9 Manual.Count131072.C018779.packed 128 cuts18779 = true := by
 decide +kernel
def pointBounds18779 : List (Nat × Nat × Nat) := [(2465347584,99203326270244,99203706154325),(2465425408,99203741166548,99204121050880)]
theorem point_links_checked18779 : (cuts18779.take 2).map (fun c => (2465333249-1+2*2^9*c.k,99203252172075+c.lower,99203632056110+c.upper)) = pointBounds18779 := by
 decide +kernel
def cuts18780 : List PrefixCut := [⟨38,202873330,202873449⟩,
⟨114,612491927,612492292⟩,
⟨128,689094195,689094605⟩]
theorem checked18780 : checkPrefixCuts (2^48) 2465464321 9 Manual.Count131072.C018780.packed 128 cuts18780 = true := by
 decide +kernel
def pointBounds18780 : List (Nat × Nat × Nat) := [(2465503232,99204152738982,99204532623554),(2465581056,99204562357579,99204942242397)]
theorem point_links_checked18780 : (cuts18780.take 2).map (fun c => (2465464321-1+2*2^9*c.k,99203949865652+c.lower,99204329750105+c.upper)) = pointBounds18780 := by
 decide +kernel
def cuts18781 : List PrefixCut := [⟨62,330263626,330263824⟩,
⟨128,689742476,689742891⟩]
theorem checked18781 : checkPrefixCuts (2^48) 2465595393 9 Manual.Count131072.C018781.packed 128 cuts18781 = true := by
 decide +kernel
def pointBounds18781 : List (Nat × Nat × Nat) := [(2465658880,99204969223473,99205349108534)]
theorem point_links_checked18781 : (cuts18781.take 1).map (fun c => (2465595393-1+2*2^9*c.k,99204638959847+c.lower,99205018844710+c.upper)) = pointBounds18781 := by
 decide +kernel
def cuts18782 : List PrefixCut := [⟨10,51027158,51027188⟩,
⟨86,464374067,464374342⟩,
⟨128,693472882,693473298⟩]
theorem checked18782 : checkPrefixCuts (2^48) 2465726465 9 Manual.Count131072.C018782.packed 128 cuts18782 = true := by
 decide +kernel
def pointBounds18782 : List (Nat × Nat × Nat) := [(2465736704,99205379729481,99205759614789),(2465814528,99205793076390,99206172961943)]
theorem point_links_checked18782 : (cuts18782.take 2).map (fun c => (2465726465-1+2*2^9*c.k,99205328702323+c.lower,99205708587601+c.upper)) = pointBounds18782 := by
 decide +kernel
def cuts18783 : List PrefixCut := [⟨34,182979358,182979468⟩,
⟨110,596756632,596756989⟩,
⟨128,695490535,695490951⟩]
theorem checked18783 : checkPrefixCuts (2^48) 2465857537 9 Manual.Count131072.C018783.packed 128 cuts18783 = true := by
 decide +kernel
def pointBounds18783 : List (Nat × Nat × Nat) := [(2465892352,99206205154563,99206585040367),(2465970176,99206618931837,99206998817888)]
theorem point_links_checked18783 : (cuts18783.take 2).map (fun c => (2465857537-1+2*2^9*c.k,99206022175205+c.lower,99206402060899+c.upper)) = pointBounds18783 := by
 decide +kernel
def cuts18784 : List PrefixCut := [⟨58,312633450,312633640⟩,
⟨128,698193025,698193446⟩]
theorem checked18784 : checkPrefixCuts (2^48) 2465988609 9 Manual.Count131072.C018784.packed 128 cuts18784 = true := by
 decide +kernel
def pointBounds18784 : List (Nat × Nat × Nat) := [(2466048000,99207030299190,99207410185490)]
theorem point_links_checked18784 : (cuts18784.take 1).map (fun c => (2465988609-1+2*2^9*c.k,99206717665740+c.lower,99207097551850+c.upper)) = pointBounds18784 := by
 decide +kernel
def cuts18785 : List PrefixCut := [⟨6,29561381,29561399⟩,
⟨82,447294312,447294579⟩,
⟨128,702264702,702265122⟩]
theorem checked18785 : checkPrefixCuts (2^48) 2466119681 9 Manual.Count131072.C018785.packed 128 cuts18785 = true := by
 decide +kernel
def pointBounds18785 : List (Nat × Nat × Nat) := [(2466125824,99207445420146,99207825306695),(2466203648,99207863153077,99208243039875)]
theorem point_links_checked18785 : (cuts18785.take 2).map (fun c => (2466119681-1+2*2^9*c.k,99207415858765+c.lower,99207795745296+c.upper)) = pointBounds18785 := by
 decide +kernel
def cuts18786 : List PrefixCut := [⟨30,159781958,159782057⟩,
⟨106,565961584,565961927⟩,
⟨128,688303742,688304160⟩]
theorem checked18786 : checkPrefixCuts (2^48) 2466250753 9 Manual.Count131072.C018786.packed 128 cuts18786 = true := by
 decide +kernel
def pointBounds18786 : List (Nat × Nat × Nat) := [(2466281472,99208277905425,99208657792475),(2466359296,99208684085051,99209063972345)]
theorem point_links_checked18786 : (cuts18786.take 2).map (fun c => (2466250753-1+2*2^9*c.k,99208118123467+c.lower,99208498010418+c.upper)) = pointBounds18786 := by
 decide +kernel
def cuts18787 : List PrefixCut := [⟨54,293753527,293753702⟩,
⟨128,694087597,694088009⟩]
theorem checked18787 : checkPrefixCuts (2^48) 2466381825 9 Manual.Count131072.C018787.packed 128 cuts18787 = true := by
 decide +kernel
def pointBounds18787 : List (Nat × Nat × Nat) := [(2466437120,99209100180736,99209480068280)]
theorem point_links_checked18787 : (cuts18787.take 1).map (fun c => (2466381825-1+2*2^9*c.k,99208806427209+c.lower,99209186314578+c.upper)) = pointBounds18787 := by
 decide +kernel
def cuts18788 : List PrefixCut := [⟨2,12210680,12210688⟩,
⟨78,414015504,414015753⟩,
⟨128,688116570,688116983⟩]
theorem checked18788 : checkPrefixCuts (2^48) 2466512897 9 Manual.Count131072.C018788.packed 128 cuts18788 = true := by
 decide +kernel
def pointBounds18788 : List (Nat × Nat × Nat) := [(2466514944,99209512725486,99209892613275),(2466592768,99209914530310,99210294418340)]
theorem point_links_checked18788 : (cuts18788.take 2).map (fun c => (2466512897-1+2*2^9*c.k,99209500514806+c.lower,99209880402587+c.upper)) = pointBounds18788 := by
 decide +kernel
def cuts18789 : List PrefixCut := [⟨26,138075371,138075453⟩,
⟨102,543163955,543164283⟩,
⟨128,682716887,682717298⟩]
theorem checked18789 : checkPrefixCuts (2^48) 2466643969 9 Manual.Count131072.C018789.packed 128 cuts18789 = true := by
 decide +kernel
def pointBounds18789 : List (Nat × Nat × Nat) := [(2466670592,99210326706747,99210706595023),(2466748416,99210731795331,99211111683853)]
theorem point_links_checked18789 : (cuts18789.take 2).map (fun c => (2466643969-1+2*2^9*c.k,99210188631376+c.lower,99210568519570+c.upper)) = pointBounds18789 := by
 decide +kernel
def cuts18790 : List PrefixCut := [⟨50,264381858,264382018⟩,
⟨126,685076954,685077365⟩,
⟨128,695916493,695916910⟩]
theorem checked18790 : checkPrefixCuts (2^48) 2466775041 9 Manual.Count131072.C018790.packed 128 cuts18790 = true := by
 decide +kernel
def pointBounds18790 : List (Nat × Nat × Nat) := [(2466826240,99211135730121,99211515618886),(2466904064,99211556425217,99211936314233)]
theorem point_links_checked18790 : (cuts18790.take 2).map (fun c => (2466775041-1+2*2^9*c.k,99210871348263+c.lower,99211251236868+c.upper)) = pointBounds18790 := by
 decide +kernel
def cuts18791 : List PrefixCut := [⟨74,396264467,396264708⟩,
⟨128,690402886,690403301⟩]
theorem checked18791 : checkPrefixCuts (2^48) 2466906113 9 Manual.Count131072.C018791.packed 128 cuts18791 = true := by
 decide +kernel
def pointBounds18791 : List (Nat × Nat × Nat) := [(2466981888,99211963529223,99212343418486)]
theorem point_links_checked18791 : (cuts18791.take 1).map (fun c => (2466906113-1+2*2^9*c.k,99211567264756+c.lower,99211947153778+c.upper)) = pointBounds18791 := by
 decide +kernel
def cuts18792 : List PrefixCut := [⟨22,120825311,120825383⟩,
⟨98,532695528,532695848⟩,
⟨128,692762358,692762776⟩]
theorem checked18792 : checkPrefixCuts (2^48) 2467037185 9 Manual.Count131072.C018792.packed 128 cuts18792 = true := by
 decide +kernel
def pointBounds18792 : List (Nat × Nat × Nat) := [(2467059712,99212378492953,99212758382462),(2467137536,99212790363170,99213170252927)]
theorem point_links_checked18792 : (cuts18792.take 2).map (fun c => (2467037185-1+2*2^9*c.k,99212257667642+c.lower,99212637557079+c.upper)) = pointBounds18792 := by
 decide +kernel
def cuts18793 : List PrefixCut := [⟨46,249052242,249052391⟩,
⟨122,652796492,652796884⟩,
⟨128,686564859,686565271⟩]
theorem checked18793 : checkPrefixCuts (2^48) 2467168257 9 Manual.Count131072.C018793.packed 128 cuts18793 = true := by
 decide +kernel
def pointBounds18793 : List (Nat × Nat × Nat) := [(2467215360,99213199482242,99213579372246),(2467293184,99213603226492,99213983116739)]
theorem point_links_checked18793 : (cuts18793.take 2).map (fun c => (2467168257-1+2*2^9*c.k,99212950430000+c.lower,99213330319855+c.upper)) = pointBounds18793 := by
 decide +kernel
def cuts18794 : List PrefixCut := [⟨70,377150205,377150438⟩,
⟨128,689266231,689266646⟩]
theorem checked18794 : checkPrefixCuts (2^48) 2467299329 9 Manual.Count131072.C018794.packed 128 cuts18794 = true := by
 decide +kernel
def pointBounds18794 : List (Nat × Nat × Nat) := [(2467371008,99214014145064,99214394035564)]
theorem point_links_checked18794 : (cuts18794.take 1).map (fun c => (2467299329-1+2*2^9*c.k,99213636994859+c.lower,99214016885126+c.upper)) = pointBounds18794 := by
 decide +kernel
def cuts18795 : List PrefixCut := [⟨18,97192499,97192557⟩,
⟨94,509910272,509910580⟩,
⟨128,692879946,692880365⟩]
theorem checked18795 : checkPrefixCuts (2^48) 2467430401 9 Manual.Count131072.C018795.packed 128 cuts18795 = true := by
 decide +kernel
def pointBounds18795 : List (Nat × Nat × Nat) := [(2467448832,99214423453589,99214803344329),(2467526656,99214836171362,99215216062352)]
theorem point_links_checked18795 : (cuts18795.take 2).map (fun c => (2467430401-1+2*2^9*c.k,99214326261090+c.lower,99214706151772+c.upper)) = pointBounds18795 := by
 decide +kernel
def cuts18796 : List PrefixCut := [⟨42,221293991,221294125⟩,
⟨118,635126461,635126840⟩,
⟨128,692044515,692044929⟩]
theorem checked18796 : checkPrefixCuts (2^48) 2467561473 9 Manual.Count131072.C018796.packed 128 cuts18796 = true := by
 decide +kernel
def pointBounds18796 : List (Nat × Nat × Nat) := [(2467604480,99215240435027,99215620326262),(2467682304,99215654267497,99216034158977)]
theorem point_links_checked18796 : (cuts18796.take 2).map (fun c => (2467561473-1+2*2^9*c.k,99215019141036+c.lower,99215399032137+c.upper)) = pointBounds18796 := by
 decide +kernel
def cuts18797 : List PrefixCut := [⟨66,353251415,353251630⟩,
⟨128,687217374,687217787⟩]
theorem checked18797 : checkPrefixCuts (2^48) 2467692545 9 Manual.Count131072.C018797.packed 128 cuts18797 = true := by
 decide +kernel
def pointBounds18797 : List (Nat × Nat × Nat) := [(2467760128,99216064436966,99216444328696)]
theorem point_links_checked18797 : (cuts18797.take 1).map (fun c => (2467692545-1+2*2^9*c.k,99215711185551+c.lower,99216091077066+c.upper)) = pointBounds18797 := by
 decide +kernel
def cuts18798 : List PrefixCut := [⟨14,78243525,78243572⟩,
⟨90,487018396,487018690⟩,
⟨128,692085324,692085741⟩]
theorem checked18798 : checkPrefixCuts (2^48) 2467823617 9 Manual.Count131072.C018798.packed 128 cuts18798 = true := by
 decide +kernel
def pointBounds18798 : List (Nat × Nat × Nat) := [(2467837952,99216476646450,99216856538425),(2467915776,99216885421321,99217265313543)]
theorem point_links_checked18798 : (cuts18798.take 2).map (fun c => (2467823617-1+2*2^9*c.k,99216398402925+c.lower,99216778294853+c.upper)) = pointBounds18798 := by
 decide +kernel
def cuts18799 : List PrefixCut := [⟨38,206318237,206318360⟩,
⟨114,623620944,623621318⟩,
⟨128,697180725,697181145⟩]
theorem checked18799 : checkPrefixCuts (2^48) 2467954689 9 Manual.Count131072.C018799.packed 128 cuts18799 = true := by
 decide +kernel
def pointBounds18799 : List (Nat × Nat × Nat) := [(2467993600,99217296806486,99217676698954),(2468071424,99217714109193,99218094001912)]
theorem point_links_checked18799 : (cuts18799.take 2).map (fun c => (2467954689-1+2*2^9*c.k,99217090488249+c.lower,99217470380594+c.upper)) = pointBounds18799 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000274
