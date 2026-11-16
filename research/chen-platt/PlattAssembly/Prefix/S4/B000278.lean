import PlattAssemblyKernel
import PlattCertificates.Count131072.C038896
import PlattCertificates.Count131072.C038897
import PlattCertificates.Count131072.C038898
import PlattCertificates.Count131072.C038899
import PlattCertificates.Count131072.C038900
import PlattCertificates.Count131072.C038901
import PlattCertificates.Count131072.C038902
import PlattCertificates.Count131072.C038903
import PlattCertificates.Count131072.C038904
import PlattCertificates.Count131072.C038905
import PlattCertificates.Count131072.C038906
import PlattCertificates.Count131072.C038907
import PlattCertificates.Count131072.C038908
import PlattCertificates.Count131072.C038909
import PlattCertificates.Count131072.C038910
import PlattCertificates.Count131072.C038911
import PlattCertificates.Count131072.C038912
import PlattCertificates.Count131072.C038913
import PlattCertificates.Count131072.C038914
import PlattCertificates.Count131072.C038915
import PlattCertificates.Count131072.C038916
import PlattCertificates.Count131072.C038917
import PlattCertificates.Count131072.C038918
import PlattCertificates.Count131072.C038919
import PlattCertificates.Count131072.C038920
import PlattCertificates.Count131072.C038921
import PlattCertificates.Count131072.C038922
import PlattCertificates.Count131072.C038923
import PlattCertificates.Count131072.C038924
import PlattCertificates.Count131072.C038925
import PlattCertificates.Count131072.C038926
import PlattCertificates.Count131072.C038927
namespace ChenEffective.PlattWindow.Assembly.Prefix.S4.B000278
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts38896 : List PrefixCut := [⟨64,323006511,323006706⟩]
theorem checked38896 : checkPrefixCuts (2^48) 5102108673 10 Manual.Count131072.C038896.packed 64 cuts38896 = true := by
 decide +kernel
def cuts38897 : List PrefixCut := [⟨3,15888066,15888075⟩,
⟨64,325425538,325425736⟩]
theorem checked38897 : checkPrefixCuts (2^48) 5102239745 10 Manual.Count131072.C038897.packed 64 cuts38897 = true := by
 decide +kernel
def pointBounds38897 : List (Nat × Nat × Nat) := [(5102245888,108514591210232,108514976506168)]
theorem point_links_checked38897 : (cuts38897.take 1).map (fun c => (5102239745-1+2*2^10*c.k,108514575322166+c.lower,108514960618093+c.upper)) = pointBounds38897 := by
 decide +kernel
def cuts38898 : List PrefixCut := [⟨17,87547361,87547415⟩,
⟨64,321003981,321004176⟩]
theorem checked38898 : checkPrefixCuts (2^48) 5102370817 10 Manual.Count131072.C038898.packed 64 cuts38898 = true := by
 decide +kernel
def pointBounds38898 : List (Nat × Nat × Nat) := [(5102405632,108514988295065,108515373591244)]
theorem point_links_checked38898 : (cuts38898.take 1).map (fun c => (5102370817-1+2*2^10*c.k,108514900747704+c.lower,108515286043829+c.upper)) = pointBounds38898 := by
 decide +kernel
def cuts38899 : List PrefixCut := [⟨31,155451447,155451542⟩,
⟨64,323091939,323092130⟩]
theorem checked38899 : checkPrefixCuts (2^48) 5102501889 10 Manual.Count131072.C038899.packed 64 cuts38899 = true := by
 decide +kernel
def pointBounds38899 : List (Nat × Nat × Nat) := [(5102565376,108515377203132,108515762499547)]
theorem point_links_checked38899 : (cuts38899.take 1).map (fun c => (5102501889-1+2*2^10*c.k,108515221751685+c.lower,108515607048005+c.upper)) = pointBounds38899 := by
 decide +kernel
def cuts38900 : List PrefixCut := [⟨45,228867872,228868010⟩,
⟨64,325069473,325069670⟩]
theorem checked38900 : checkPrefixCuts (2^48) 5102632961 10 Manual.Count131072.C038900.packed 64 cuts38900 = true := by
 decide +kernel
def pointBounds38900 : List (Nat × Nat × Nat) := [(5102725120,108515773711496,108516159008145)]
theorem point_links_checked38900 : (cuts38900.take 1).map (fun c => (5102632961-1+2*2^10*c.k,108515544843624+c.lower,108515930140135+c.upper)) = pointBounds38900 := by
 decide +kernel
def cuts38901 : List PrefixCut := [⟨59,297812140,297812317⟩,
⟨64,322303134,322303325⟩]
theorem checked38901 : checkPrefixCuts (2^48) 5102764033 10 Manual.Count131072.C038901.packed 64 cuts38901 = true := by
 decide +kernel
def pointBounds38901 : List (Nat × Nat × Nat) := [(5102884864,108516167725237,108516553022122)]
theorem point_links_checked38901 : (cuts38901.take 1).map (fun c => (5102764033-1+2*2^10*c.k,108515869913097+c.lower,108516255209805+c.upper)) = pointBounds38901 := by
 decide +kernel
def cuts38902 : List PrefixCut := [⟨64,326652411,326652603⟩]
theorem checked38902 : checkPrefixCuts (2^48) 5102895105 10 Manual.Count131072.C038902.packed 64 cuts38902 = true := by
 decide +kernel
def cuts38903 : List PrefixCut := [⟨9,45395302,45395330⟩,
⟨64,321569498,321569692⟩]
theorem checked38903 : checkPrefixCuts (2^48) 5103026177 10 Manual.Count131072.C038903.packed 64 cuts38903 = true := by
 decide +kernel
def pointBounds38903 : List (Nat × Nat × Nat) := [(5103044608,108516564263944,108516949561063)]
theorem point_links_checked38903 : (cuts38903.take 1).map (fun c => (5103026177-1+2*2^10*c.k,108516518868642+c.lower,108516904165733+c.upper)) = pointBounds38903 := by
 decide +kernel
def cuts38904 : List PrefixCut := [⟨23,118256079,118256147⟩,
⟨64,323767488,323767682⟩]
theorem checked38904 : checkPrefixCuts (2^48) 5103157249 10 Manual.Count131072.C038904.packed 64 cuts38904 = true := by
 decide +kernel
def pointBounds38904 : List (Nat × Nat × Nat) := [(5103204352,108516958694219,108517343991572)]
theorem point_links_checked38904 : (cuts38904.take 1).map (fun c => (5103157249-1+2*2^10*c.k,108516840438140+c.lower,108517225735425+c.upper)) = pointBounds38904 := by
 decide +kernel
def cuts38905 : List PrefixCut := [⟨37,185431733,185431845⟩,
⟨64,322269987,322270182⟩]
theorem checked38905 : checkPrefixCuts (2^48) 5103288321 10 Manual.Count131072.C038905.packed 64 cuts38905 = true := by
 decide +kernel
def pointBounds38905 : List (Nat × Nat × Nat) := [(5103364096,108517349637361,108517734934952)]
theorem point_links_checked38905 : (cuts38905.take 1).map (fun c => (5103288321-1+2*2^10*c.k,108517164205628+c.lower,108517549503107+c.upper)) = pointBounds38905 := by
 decide +kernel
def cuts38906 : List PrefixCut := [⟨51,259994134,259994288⟩,
⟨64,324412723,324412918⟩]
theorem checked38906 : checkPrefixCuts (2^48) 5103419393 10 Manual.Count131072.C038906.packed 64 cuts38906 = true := by
 decide +kernel
def pointBounds38906 : List (Nat × Nat × Nat) := [(5103523840,108517746469749,108518131767577)]
theorem point_links_checked38906 : (cuts38906.take 1).map (fun c => (5103419393-1+2*2^10*c.k,108517486475615+c.lower,108517871773289+c.upper)) = pointBounds38906 := by
 decide +kernel
def cuts38907 : List PrefixCut := [⟨64,322474057,322474248⟩]
theorem checked38907 : checkPrefixCuts (2^48) 5103550465 10 Manual.Count131072.C038907.packed 64 cuts38907 = true := by
 decide +kernel
def cuts38908 : List PrefixCut := [⟨1,4577561,4577563⟩,
⟨64,325609320,325609515⟩]
theorem checked38908 : checkPrefixCuts (2^48) 5103681537 10 Manual.Count131072.C038908.packed 64 cuts38908 = true := by
 decide +kernel
def pointBounds38908 : List (Nat × Nat × Nat) := [(5103683584,108518137939956,108518523238018)]
theorem point_links_checked38908 : (cuts38908.take 1).map (fun c => (5103681537-1+2*2^10*c.k,108518133362395+c.lower,108518518660455+c.upper)) = pointBounds38908 := by
 decide +kernel
def cuts38909 : List PrefixCut := [⟨15,76547870,76547915⟩,
⟨64,324828923,324829119⟩]
theorem checked38909 : checkPrefixCuts (2^48) 5103812609 10 Manual.Count131072.C038909.packed 64 cuts38909 = true := by
 decide +kernel
def pointBounds38909 : List (Nat × Nat × Nat) := [(5103843328,108518535519585,108518920817885)]
theorem point_links_checked38909 : (cuts38909.take 1).map (fun c => (5103812609-1+2*2^10*c.k,108518458971715+c.lower,108518844269970+c.upper)) = pointBounds38909 := by
 decide +kernel
def cuts38910 : List PrefixCut := [⟨29,144653711,144653796⟩,
⟨64,322228616,322228807⟩]
theorem checked38910 : checkPrefixCuts (2^48) 5103943681 10 Manual.Count131072.C038910.packed 64 cuts38910 = true := by
 decide +kernel
def pointBounds38910 : List (Nat × Nat × Nat) := [(5104003072,108518928454349,108519313752885)]
theorem point_links_checked38910 : (cuts38910.take 1).map (fun c => (5103943681-1+2*2^10*c.k,108518783800638+c.lower,108519169099089+c.upper)) = pointBounds38910 := by
 decide +kernel
def cuts38911 : List PrefixCut := [⟨43,217994565,217994698⟩,
⟨64,323157819,323158015⟩]
theorem checked38911 : checkPrefixCuts (2^48) 5104074753 10 Manual.Count131072.C038911.packed 64 cuts38911 = true := by
 decide +kernel
def pointBounds38911 : List (Nat × Nat × Nat) := [(5104162816,108519324023819,108519709322594)]
theorem point_links_checked38911 : (cuts38911.take 1).map (fun c => (5104074753-1+2*2^10*c.k,108519106029254+c.lower,108519491327896+c.upper)) = pointBounds38911 := by
 decide +kernel
def cuts38912 : List PrefixCut := [⟨57,289235784,289235961⟩,
⟨64,325079606,325079804⟩]
theorem checked38912 : checkPrefixCuts (2^48) 5104205825 10 Manual.Count131072.C038912.packed 64 cuts38912 = true := by
 decide +kernel
def pointBounds38912 : List (Nat × Nat × Nat) := [(5104322560,108519718422857,108520103721872)]
theorem point_links_checked38912 : (cuts38912.take 1).map (fun c => (5104205825-1+2*2^10*c.k,108519429187073+c.lower,108519814485911+c.upper)) = pointBounds38912 := by
 decide +kernel
def cuts38913 : List PrefixCut := [⟨64,324409550,324409744⟩]
theorem checked38913 : checkPrefixCuts (2^48) 5104336897 10 Manual.Count131072.C038913.packed 64 cuts38913 = true := by
 decide +kernel
def cuts38914 : List PrefixCut := [⟨7,36890513,36890535⟩,
⟨64,323904933,323905125⟩]
theorem checked38914 : checkPrefixCuts (2^48) 5104467969 10 Manual.Count131072.C038914.packed 64 cuts38914 = true := by
 decide +kernel
def pointBounds38914 : List (Nat × Nat × Nat) := [(5104482304,108520115566742,108520500865994)]
theorem point_links_checked38914 : (cuts38914.take 1).map (fun c => (5104467969-1+2*2^10*c.k,108520078676229+c.lower,108520463975459+c.upper)) = pointBounds38914 := by
 decide +kernel
def cuts38915 : List PrefixCut := [⟨21,105650535,105650597⟩,
⟨64,325771371,325771565⟩]
theorem checked38915 : checkPrefixCuts (2^48) 5104599041 10 Manual.Count131072.C038915.packed 64 cuts38915 = true := by
 decide +kernel
def pointBounds38915 : List (Nat × Nat × Nat) := [(5104642048,108520508231697,108520893531181)]
theorem point_links_checked38915 : (cuts38915.take 1).map (fun c => (5104599041-1+2*2^10*c.k,108520402581162+c.lower,108520787880584+c.upper)) = pointBounds38915 := by
 decide +kernel
def cuts38916 : List PrefixCut := [⟨35,178928094,178928201⟩,
⟨64,325321915,325322107⟩]
theorem checked38916 : checkPrefixCuts (2^48) 5104730113 10 Manual.Count131072.C038916.packed 64 cuts38916 = true := by
 decide +kernel
def pointBounds38916 : List (Nat × Nat × Nat) := [(5104801792,108520907280627,108521292580350)]
theorem point_links_checked38916 : (cuts38916.take 1).map (fun c => (5104730113-1+2*2^10*c.k,108520728352533+c.lower,108521113652149+c.upper)) = pointBounds38916 := by
 decide +kernel
def cuts38917 : List PrefixCut := [⟨49,249995963,249996111⟩,
⟨64,325423857,325424050⟩]
theorem checked38917 : checkPrefixCuts (2^48) 5104861185 10 Manual.Count131072.C038917.packed 64 cuts38917 = true := by
 decide +kernel
def pointBounds38917 : List (Nat × Nat × Nat) := [(5104961536,108521303670411,108521688970367)]
theorem point_links_checked38917 : (cuts38917.take 1).map (fun c => (5104861185-1+2*2^10*c.k,108521053674448+c.lower,108521438974256+c.upper)) = pointBounds38917 := by
 decide +kernel
def cuts38918 : List PrefixCut := [⟨63,322713878,322714070⟩,
⟨64,327069604,327069799⟩]
theorem checked38918 : checkPrefixCuts (2^48) 5104992257 10 Manual.Count131072.C038918.packed 64 cuts38918 = true := by
 decide +kernel
def pointBounds38918 : List (Nat × Nat × Nat) := [(5105121280,108521701812183,108522087112376)]
theorem point_links_checked38918 : (cuts38918.take 1).map (fun c => (5104992257-1+2*2^10*c.k,108521379098305+c.lower,108521764398306+c.upper)) = pointBounds38918 := by
 decide +kernel
def cuts38919 : List PrefixCut := [⟨64,323863355,323863546⟩]
theorem checked38919 : checkPrefixCuts (2^48) 5105123329 10 Manual.Count131072.C038919.packed 64 cuts38919 = true := by
 decide +kernel
def cuts38920 : List PrefixCut := [⟨13,66932932,66932972⟩,
⟨64,325288541,325288736⟩]
theorem checked38920 : checkPrefixCuts (2^48) 5105254401 10 Manual.Count131072.C038920.packed 64 cuts38920 = true := by
 decide +kernel
def pointBounds38920 : List (Nat × Nat × Nat) := [(5105281024,108522096964196,108522482264623)]
theorem point_links_checked38920 : (cuts38920.take 1).map (fun c => (5105254401-1+2*2^10*c.k,108522030031264+c.lower,108522415331651+c.upper)) = pointBounds38920 := by
 decide +kernel
def cuts38921 : List PrefixCut := [⟨27,136012214,136012296⟩,
⟨64,319766935,319767127⟩]
theorem checked38921 : checkPrefixCuts (2^48) 5105385473 10 Manual.Count131072.C038921.packed 64 cuts38921 = true := by
 decide +kernel
def pointBounds38921 : List (Nat × Nat × Nat) := [(5105440768,108522491332019,108522876632683)]
theorem point_links_checked38921 : (cuts38921.take 1).map (fun c => (5105385473-1+2*2^10*c.k,108522355319805+c.lower,108522740620387+c.upper)) = pointBounds38921 := by
 decide +kernel
def cuts38922 : List PrefixCut := [⟨41,209994258,209994382⟩,
⟨64,325051321,325051513⟩]
theorem checked38922 : checkPrefixCuts (2^48) 5105516545 10 Manual.Count131072.C038922.packed 64 cuts38922 = true := by
 decide +kernel
def pointBounds38922 : List (Nat × Nat × Nat) := [(5105600512,108522885080998,108523270381896)]
theorem point_links_checked38922 : (cuts38922.take 1).map (fun c => (5105516545-1+2*2^10*c.k,108522675086740+c.lower,108523060387514+c.upper)) = pointBounds38922 := by
 decide +kernel
def cuts38923 : List PrefixCut := [⟨55,283806687,283806859⟩,
⟨64,331493091,331493290⟩]
theorem checked38923 : checkPrefixCuts (2^48) 5105647617 10 Manual.Count131072.C038923.packed 64 cuts38923 = true := by
 decide +kernel
def pointBounds38923 : List (Nat × Nat × Nat) := [(5105760256,108523283944748,108523669245886)]
theorem point_links_checked38923 : (cuts38923.take 1).map (fun c => (5105647617-1+2*2^10*c.k,108523000138061+c.lower,108523385439027+c.upper)) = pointBounds38923 := by
 decide +kernel
def cuts38924 : List PrefixCut := [⟨64,321837125,321837319⟩]
theorem checked38924 : checkPrefixCuts (2^48) 5105778689 10 Manual.Count131072.C038924.packed 64 cuts38924 = true := by
 decide +kernel
def cuts38925 : List PrefixCut := [⟨5,24917504,24917520⟩,
⟨64,323978812,323979010⟩]
theorem checked38925 : checkPrefixCuts (2^48) 5105909761 10 Manual.Count131072.C038925.packed 64 cuts38925 = true := by
 decide +kernel
def pointBounds38925 : List (Nat × Nat × Nat) := [(5105920000,108523678385781,108524063687156)]
theorem point_links_checked38925 : (cuts38925.take 1).map (fun c => (5105909761-1+2*2^10*c.k,108523653468277+c.lower,108524038769636+c.upper)) = pointBounds38925 := by
 decide +kernel
def cuts38926 : List PrefixCut := [⟨19,93382844,93382900⟩,
⟨64,323474343,323474538⟩]
theorem checked38926 : checkPrefixCuts (2^48) 5106040833 10 Manual.Count131072.C038926.packed 64 cuts38926 = true := by
 decide +kernel
def pointBounds38926 : List (Nat × Nat × Nat) := [(5106079744,108524070829933,108524456131546)]
theorem point_links_checked38926 : (cuts38926.take 1).map (fun c => (5106040833-1+2*2^10*c.k,108523977447089+c.lower,108524362748646+c.upper)) = pointBounds38926 := by
 decide +kernel
def cuts38927 : List PrefixCut := [⟨33,163498014,163498114⟩,
⟨64,319772771,319772965⟩]
theorem checked38927 : checkPrefixCuts (2^48) 5106171905 10 Manual.Count131072.C038927.packed 64 cuts38927 = true := by
 decide +kernel
def pointBounds38927 : List (Nat × Nat × Nat) := [(5106239488,108524464419446,108524849721298)]
theorem point_links_checked38927 : (cuts38927.take 1).map (fun c => (5106171905-1+2*2^10*c.k,108524300921432+c.lower,108524686223184+c.upper)) = pointBounds38927 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S4.B000278
