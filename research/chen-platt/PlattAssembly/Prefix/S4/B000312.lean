import PlattAssemblyKernel
import PlattCertificates.Count131072.C039984
import PlattCertificates.Count131072.C039985
import PlattCertificates.Count131072.C039986
import PlattCertificates.Count131072.C039987
import PlattCertificates.Count131072.C039988
import PlattCertificates.Count131072.C039989
import PlattCertificates.Count131072.C039990
import PlattCertificates.Count131072.C039991
import PlattCertificates.Count131072.C039992
import PlattCertificates.Count131072.C039993
import PlattCertificates.Count131072.C039994
import PlattCertificates.Count131072.C039995
import PlattCertificates.Count131072.C039996
import PlattCertificates.Count131072.C039997
import PlattCertificates.Count131072.C039998
import PlattCertificates.Count131072.C039999
namespace ChenEffective.PlattWindow.Assembly.Prefix.S4.B000312
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts39984 : List PrefixCut := [⟨64,311325842,311326025⟩]
theorem checked39984 : checkPrefixCuts (2^48) 5244715009 10 Manual.Count131072.C039984.packed 64 cuts39984 = true := by
 decide +kernel
def cuts39985 : List PrefixCut := [⟨15,73630842,73630884⟩,
⟨64,317972720,317972904⟩]
theorem checked39985 : checkPrefixCuts (2^48) 5244846081 10 Manual.Count131072.C039985.packed 64 cuts39985 = true := by
 decide +kernel
def pointBounds39985 : List (Nat × Nat × Nat) := [(5244876800,108861595155338,108861980658179)]
theorem point_links_checked39985 : (cuts39985.take 1).map (fun c => (5244846081-1+2*2^10*c.k,108861521524496+c.lower,108861907027295+c.upper)) = pointBounds39985 := by
 decide +kernel
def cuts39986 : List PrefixCut := [⟨32,157078252,157078345⟩,
⟨64,315925471,315925659⟩]
theorem checked39986 : checkPrefixCuts (2^48) 5244977153 10 Manual.Count131072.C039986.packed 64 cuts39986 = true := by
 decide +kernel
def pointBounds39986 : List (Nat × Nat × Nat) := [(5245042688,108861996575468,108862382078544)]
theorem point_links_checked39986 : (cuts39986.take 1).map (fun c => (5244977153-1+2*2^10*c.k,108861839497216+c.lower,108862225000199+c.upper)) = pointBounds39986 := by
 decide +kernel
def cuts39987 : List PrefixCut := [⟨49,240359941,240360082⟩,
⟨64,313932028,313932212⟩]
theorem checked39987 : checkPrefixCuts (2^48) 5245108225 10 Manual.Count131072.C039987.packed 64 cuts39987 = true := by
 decide +kernel
def pointBounds39987 : List (Nat × Nat × Nat) := [(5245208576,108862395782628,108862781285940)]
theorem point_links_checked39987 : (cuts39987.take 1).map (fun c => (5245108225-1+2*2^10*c.k,108862155422687+c.lower,108862540925858+c.upper)) = pointBounds39987 := by
 decide +kernel
def cuts39988 : List PrefixCut := [⟨64,311724080,311724265⟩]
theorem checked39988 : checkPrefixCuts (2^48) 5245239297 10 Manual.Count131072.C039988.packed 64 cuts39988 = true := by
 decide +kernel
def cuts39989 : List PrefixCut := [⟨2,10195697,10195703⟩,
⟨64,313326062,313326250⟩]
theorem checked39989 : checkPrefixCuts (2^48) 5245370369 10 Manual.Count131072.C039989.packed 64 cuts39989 = true := by
 decide +kernel
def pointBounds39989 : List (Nat × Nat × Nat) := [(5245374464,108862791274492,108863176778038)]
theorem point_links_checked39989 : (cuts39989.take 1).map (fun c => (5245370369-1+2*2^10*c.k,108862781078795+c.lower,108863166582335+c.upper)) = pointBounds39989 := by
 decide +kernel
def cuts39990 : List PrefixCut := [⟨19,93100175,93100232⟩,
⟨64,314284118,314284311⟩]
theorem checked39990 : checkPrefixCuts (2^48) 5245501441 10 Manual.Count131072.C039990.packed 64 cuts39990 = true := by
 decide +kernel
def pointBounds39990 : List (Nat × Nat × Nat) := [(5245540352,108863187505032,108863573008817)]
theorem point_links_checked39990 : (cuts39990.take 1).map (fun c => (5245501441-1+2*2^10*c.k,108863094404857+c.lower,108863479908585+c.upper)) = pointBounds39990 := by
 decide +kernel
def cuts39991 : List PrefixCut := [⟨36,173370700,173370805⟩,
⟨64,311486035,311486220⟩]
theorem checked39991 : checkPrefixCuts (2^48) 5245632513 10 Manual.Count131072.C039991.packed 64 cuts39991 = true := by
 decide +kernel
def pointBounds39991 : List (Nat × Nat × Nat) := [(5245706240,108863582059675,108863967563701)]
theorem point_links_checked39991 : (cuts39991.take 1).map (fun c => (5245632513-1+2*2^10*c.k,108863408688975+c.lower,108863794192896+c.upper)) = pointBounds39991 := by
 decide +kernel
def cuts39992 : List PrefixCut := [⟨53,260182818,260182972⟩,
⟨64,313195281,313195465⟩]
theorem checked39992 : checkPrefixCuts (2^48) 5245763585 10 Manual.Count131072.C039992.packed 64 cuts39992 = true := by
 decide +kernel
def pointBounds39992 : List (Nat × Nat × Nat) := [(5245872128,108863980357828,108864365862088)]
theorem point_links_checked39992 : (cuts39992.take 1).map (fun c => (5245763585-1+2*2^10*c.k,108863720175010+c.lower,108864105679116+c.upper)) = pointBounds39992 := by
 decide +kernel
def cuts39993 : List PrefixCut := [⟨64,319948067,319948255⟩]
theorem checked39993 : checkPrefixCuts (2^48) 5245894657 10 Manual.Count131072.C039993.packed 64 cuts39993 = true := by
 decide +kernel
def cuts39994 : List PrefixCut := [⟨6,29510149,29510168⟩,
⟨64,310604232,310604421⟩]
theorem checked39994 : checkPrefixCuts (2^48) 5246025729 10 Manual.Count131072.C039994.packed 64 cuts39994 = true := by
 decide +kernel
def pointBounds39994 : List (Nat × Nat × Nat) := [(5246038016,108864382828507,108864768333004)]
theorem point_links_checked39994 : (cuts39994.take 1).map (fun c => (5246025729-1+2*2^10*c.k,108864353318358+c.lower,108864738822836+c.upper)) = pointBounds39994 := by
 decide +kernel
def cuts39995 : List PrefixCut := [⟨23,109935609,109935677⟩,
⟨64,313869246,313869432⟩]
theorem checked39995 : checkPrefixCuts (2^48) 5246156801 10 Manual.Count131072.C039995.packed 64 cuts39995 = true := by
 decide +kernel
def pointBounds39995 : List (Nat × Nat × Nat) := [(5246203904,108864773858199,108865159362934)]
theorem point_links_checked39995 : (cuts39995.take 1).map (fun c => (5246156801-1+2*2^10*c.k,108864663922590+c.lower,108865049427257+c.upper)) = pointBounds39995 := by
 decide +kernel
def cuts39996 : List PrefixCut := [⟨40,192502613,192502728⟩,
⟨64,310803317,310803502⟩]
theorem checked39996 : checkPrefixCuts (2^48) 5246287873 10 Manual.Count131072.C039996.packed 64 cuts39996 = true := by
 decide +kernel
def pointBounds39996 : List (Nat × Nat × Nat) := [(5246369792,108865170294449,108865555799417)]
theorem point_links_checked39996 : (cuts39996.take 1).map (fun c => (5246287873-1+2*2^10*c.k,108864977791836+c.lower,108865363296689+c.upper)) = pointBounds39996 := by
 decide +kernel
def cuts39997 : List PrefixCut := [⟨57,273830946,273831110⟩,
⟨64,307469240,307469425⟩]
theorem checked39997 : checkPrefixCuts (2^48) 5246418945 10 Manual.Count131072.C039997.packed 64 cuts39997 = true := by
 decide +kernel
def pointBounds39997 : List (Nat × Nat × Nat) := [(5246535680,108865562426099,108865947931301)]
theorem point_links_checked39997 : (cuts39997.take 1).map (fun c => (5246418945-1+2*2^10*c.k,108865288595153+c.lower,108865674100191+c.upper)) = pointBounds39997 := by
 decide +kernel
def cuts39998 : List PrefixCut := [⟨64,311646193,311646380⟩]
theorem checked39998 : checkPrefixCuts (2^48) 5246550017 10 Manual.Count131072.C039998.packed 64 cuts39998 = true := by
 decide +kernel
def cuts39999 : List PrefixCut := [⟨10,48873398,48873427⟩,
⟨64,315125472,315125659⟩]
theorem checked39999 : checkPrefixCuts (2^48) 5246681089 10 Manual.Count131072.C039999.packed 64 cuts39999 = true := by
 decide +kernel
def pointBounds39999 : List (Nat × Nat × Nat) := [(5246701568,108865956583984,108866342089423)]
theorem point_links_checked39999 : (cuts39999.take 1).map (fun c => (5246681089-1+2*2^10*c.k,108865907710586+c.lower,108866293215996+c.upper)) = pointBounds39999 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S4.B000312
