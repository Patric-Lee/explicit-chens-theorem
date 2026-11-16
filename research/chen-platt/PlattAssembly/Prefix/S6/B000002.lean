import PlattAssemblyKernel
import PlattCertificates.Count131072.C050064
import PlattCertificates.Count131072.C050065
import PlattCertificates.Count131072.C050066
import PlattCertificates.Count131072.C050067
import PlattCertificates.Count131072.C050068
import PlattCertificates.Count131072.C050069
import PlattCertificates.Count131072.C050070
import PlattCertificates.Count131072.C050071
import PlattCertificates.Count131072.C050072
import PlattCertificates.Count131072.C050073
import PlattCertificates.Count131072.C050074
import PlattCertificates.Count131072.C050075
import PlattCertificates.Count131072.C050076
import PlattCertificates.Count131072.C050077
import PlattCertificates.Count131072.C050078
import PlattCertificates.Count131072.C050079
import PlattCertificates.Count131072.C050080
import PlattCertificates.Count131072.C050081
import PlattCertificates.Count131072.C050082
import PlattCertificates.Count131072.C050083
import PlattCertificates.Count131072.C050084
import PlattCertificates.Count131072.C050085
import PlattCertificates.Count131072.C050086
import PlattCertificates.Count131072.C050087
import PlattCertificates.Count131072.C050088
import PlattCertificates.Count131072.C050089
import PlattCertificates.Count131072.C050090
import PlattCertificates.Count131072.C050091
import PlattCertificates.Count131072.C050092
import PlattCertificates.Count131072.C050093
import PlattCertificates.Count131072.C050094
import PlattCertificates.Count131072.C050095
namespace ChenEffective.PlattWindow.Assembly.Prefix.S6.B000002
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts50064 : List PrefixCut := [⟨57,223302982,223303107⟩,
⟨64,248723858,248723999⟩]
theorem checked50064 : checkPrefixCuts (2^48) 6565920769 10 Manual.Count131072.C050064.packed 64 cuts50064 = true := by
 decide +kernel
def pointBounds50064 : List (Nat × Nat × Nat) := [(6566037504,111672985824883,111673372956153)]
theorem point_links_checked50064 : (cuts50064.take 1).map (fun c => (6565920769-1+2*2^10*c.k,111672762521901+c.lower,111673149653046+c.upper)) = pointBounds50064 := by
 decide +kernel
def cuts50065 : List PrefixCut := [⟨64,248375953,248376094⟩]
theorem checked50065 : checkPrefixCuts (2^48) 6566051841 10 Manual.Count131072.C050065.packed 64 cuts50065 = true := by
 decide +kernel
def cuts50066 : List PrefixCut := [⟨30,116384321,116384389⟩,
⟨64,246227635,246227781⟩]
theorem checked50066 : checkPrefixCuts (2^48) 6566182913 10 Manual.Count131072.C050066.packed 64 cuts50066 = true := by
 decide +kernel
def pointBounds50066 : List (Nat × Nat × Nat) := [(6566244352,111673376006033,111673763137528)]
theorem point_links_checked50066 : (cuts50066.take 1).map (fun c => (6566182913-1+2*2^10*c.k,111673259621712+c.lower,111673646753139+c.upper)) = pointBounds50066 := by
 decide +kernel
def cuts50067 : List PrefixCut := [⟨64,247165754,247165892⟩]
theorem checked50067 : checkPrefixCuts (2^48) 6566313985 10 Manual.Count131072.C050067.packed 64 cuts50067 = true := by
 decide +kernel
def cuts50068 : List PrefixCut := [⟨3,11702316,11702322⟩,
⟨64,249432689,249432832⟩]
theorem checked50068 : checkPrefixCuts (2^48) 6566445057 10 Manual.Count131072.C050068.packed 64 cuts50068 = true := by
 decide +kernel
def pointBounds50068 : List (Nat × Nat × Nat) := [(6566451200,111673764717417,111674151849134)]
theorem point_links_checked50068 : (cuts50068.take 1).map (fun c => (6566445057-1+2*2^10*c.k,111673753015101+c.lower,111674140146812+c.upper)) = pointBounds50068 := by
 decide +kernel
def cuts50069 : List PrefixCut := [⟨40,153626435,153626526⟩,
⟨64,246470060,246470205⟩]
theorem checked50069 : checkPrefixCuts (2^48) 6566576129 10 Manual.Count131072.C050069.packed 64 cuts50069 = true := by
 decide +kernel
def pointBounds50069 : List (Nat × Nat × Nat) := [(6566658048,111674156074225,111674543206170)]
theorem point_links_checked50069 : (cuts50069.take 1).map (fun c => (6566576129-1+2*2^10*c.k,111674002447790+c.lower,111674389579644+c.upper)) = pointBounds50069 := by
 decide +kernel
def cuts50070 : List PrefixCut := [⟨64,244536284,244536429⟩]
theorem checked50070 : checkPrefixCuts (2^48) 6566707201 10 Manual.Count131072.C050070.packed 64 cuts50070 = true := by
 decide +kernel
def cuts50071 : List PrefixCut := [⟨13,51006959,51006988⟩,
⟨64,249460623,249460760⟩]
theorem checked50071 : checkPrefixCuts (2^48) 6566838273 10 Manual.Count131072.C050071.packed 64 cuts50071 = true := by
 decide +kernel
def pointBounds50071 : List (Nat × Nat × Nat) := [(6566864896,111674544461093,111674931593266)]
theorem point_links_checked50071 : (cuts50071.take 1).map (fun c => (6566838273-1+2*2^10*c.k,111674493454134+c.lower,111674880586278+c.upper)) = pointBounds50071 := by
 decide +kernel
def cuts50072 : List PrefixCut := [⟨50,195921676,195921786⟩,
⟨64,251470127,251470267⟩]
theorem checked50072 : checkPrefixCuts (2^48) 6566969345 10 Manual.Count131072.C050072.packed 64 cuts50072 = true := by
 decide +kernel
def pointBounds50072 : List (Nat × Nat × Nat) := [(6567071744,111674938836433,111675325968824)]
theorem point_links_checked50072 : (cuts50072.take 1).map (fun c => (6566969345-1+2*2^10*c.k,111674742914757+c.lower,111675130047038+c.upper)) = pointBounds50072 := by
 decide +kernel
def cuts50073 : List PrefixCut := [⟨64,247007616,247007754⟩]
theorem checked50073 : checkPrefixCuts (2^48) 6567100417 10 Manual.Count131072.C050073.packed 64 cuts50073 = true := by
 decide +kernel
def cuts50074 : List PrefixCut := [⟨23,86920805,86920854⟩,
⟨64,247774120,247774262⟩]
theorem checked50074 : checkPrefixCuts (2^48) 6567231489 10 Manual.Count131072.C050074.packed 64 cuts50074 = true := by
 decide +kernel
def pointBounds50074 : List (Nat × Nat × Nat) := [(6567278592,111675328313305,111675715445913)]
theorem point_links_checked50074 : (cuts50074.take 1).map (fun c => (6567231489-1+2*2^10*c.k,111675241392500+c.lower,111675628525059+c.upper)) = pointBounds50074 := by
 decide +kernel
def cuts50075 : List PrefixCut := [⟨60,232468600,232468730⟩,
⟨64,249483555,249483694⟩]
theorem checked50075 : checkPrefixCuts (2^48) 6567362561 10 Manual.Count131072.C050075.packed 64 cuts50075 = true := by
 decide +kernel
def pointBounds50075 : List (Nat × Nat × Nat) := [(6567485440,111675721635220,111676108768051)]
theorem point_links_checked50075 : (cuts50075.take 1).map (fun c => (6567362561-1+2*2^10*c.k,111675489166620+c.lower,111675876299321+c.upper)) = pointBounds50075 := by
 decide +kernel
def cuts50076 : List PrefixCut := [⟨64,249735736,249735877⟩]
theorem checked50076 : checkPrefixCuts (2^48) 6567493633 10 Manual.Count131072.C050076.packed 64 cuts50076 = true := by
 decide +kernel
def cuts50077 : List PrefixCut := [⟨33,127501723,127501800⟩,
⟨64,246516433,246516578⟩]
theorem checked50077 : checkPrefixCuts (2^48) 6567624705 10 Manual.Count131072.C050077.packed 64 cuts50077 = true := by
 decide +kernel
def pointBounds50077 : List (Nat × Nat × Nat) := [(6567692288,111676115887634,111676503020692)]
theorem point_links_checked50077 : (cuts50077.take 1).map (fun c => (6567624705-1+2*2^10*c.k,111675988385911+c.lower,111676375518892+c.upper)) = pointBounds50077 := by
 decide +kernel
def cuts50078 : List PrefixCut := [⟨64,247582960,247583103⟩]
theorem checked50078 : checkPrefixCuts (2^48) 6567755777 10 Manual.Count131072.C050078.packed 64 cuts50078 = true := by
 decide +kernel
def cuts50079 : List PrefixCut := [⟨6,21985227,21985240⟩,
⟨64,249635050,249635191⟩]
theorem checked50079 : checkPrefixCuts (2^48) 6567886849 10 Manual.Count131072.C050079.packed 64 cuts50079 = true := by
 decide +kernel
def pointBounds50079 : List (Nat × Nat × Nat) := [(6567899136,111676504470531,111676891603813)]
theorem point_links_checked50079 : (cuts50079.take 1).map (fun c => (6567886849-1+2*2^10*c.k,111676482485304+c.lower,111676869618573+c.upper)) = pointBounds50079 := by
 decide +kernel
def cuts50080 : List PrefixCut := [⟨43,167434830,167434921⟩,
⟨64,248301581,248301717⟩]
theorem checked50080 : checkPrefixCuts (2^48) 6568017921 10 Manual.Count131072.C050080.packed 64 cuts50080 = true := by
 decide +kernel
def pointBounds50080 : List (Nat × Nat × Nat) := [(6568105984,111676899555184,111677286688685)]
theorem point_links_checked50080 : (cuts50080.take 1).map (fun c => (6568017921-1+2*2^10*c.k,111676732120354+c.lower,111677119253764+c.upper)) = pointBounds50080 := by
 decide +kernel
def cuts50081 : List PrefixCut := [⟨64,249282283,249282421⟩]
theorem checked50081 : checkPrefixCuts (2^48) 6568148993 10 Manual.Count131072.C050081.packed 64 cuts50081 = true := by
 decide +kernel
def cuts50082 : List PrefixCut := [⟨16,62309080,62309114⟩,
⟨64,248677368,248677508⟩]
theorem checked50082 : checkPrefixCuts (2^48) 6568280065 10 Manual.Count131072.C050082.packed 64 cuts50082 = true := by
 decide +kernel
def pointBounds50082 : List (Nat × Nat × Nat) := [(6568312832,111677292013298,111677679147016)]
theorem point_links_checked50082 : (cuts50082.take 1).map (fun c => (6568280065-1+2*2^10*c.k,111677229704218+c.lower,111677616837902+c.upper)) = pointBounds50082 := by
 decide +kernel
def cuts50083 : List PrefixCut := [⟨53,205434701,205434819⟩,
⟨64,248586696,248586840⟩]
theorem checked50083 : checkPrefixCuts (2^48) 6568411137 10 Manual.Count131072.C050083.packed 64 cuts50083 = true := by
 decide +kernel
def pointBounds50083 : List (Nat × Nat × Nat) := [(6568519680,111677683816287,111678070950229)]
theorem point_links_checked50083 : (cuts50083.take 1).map (fun c => (6568411137-1+2*2^10*c.k,111677478381586+c.lower,111677865515410+c.upper)) = pointBounds50083 := by
 decide +kernel
def cuts50084 : List PrefixCut := [⟨64,246396305,246396447⟩]
theorem checked50084 : checkPrefixCuts (2^48) 6568542209 10 Manual.Count131072.C050084.packed 64 cuts50084 = true := by
 decide +kernel
def cuts50085 : List PrefixCut := [⟨26,104513415,104513472⟩,
⟨64,255390037,255390175⟩]
theorem checked50085 : checkPrefixCuts (2^48) 6568673281 10 Manual.Count131072.C050085.packed 64 cuts50085 = true := by
 decide +kernel
def pointBounds50085 : List (Nat × Nat × Nat) := [(6568726528,111678077878002,111678465012169)]
theorem point_links_checked50085 : (cuts50085.take 1).map (fun c => (6568673281-1+2*2^10*c.k,111677973364587+c.lower,111678360498697+c.upper)) = pointBounds50085 := by
 decide +kernel
def cuts50086 : List PrefixCut := [⟨63,243129921,243130056⟩,
⟨64,248014753,248014890⟩]
theorem checked50086 : checkPrefixCuts (2^48) 6568804353 10 Manual.Count131072.C050086.packed 64 cuts50086 = true := by
 decide +kernel
def pointBounds50086 : List (Nat × Nat × Nat) := [(6568933376,111678471884545,111678859018928)]
theorem point_links_checked50086 : (cuts50086.take 1).map (fun c => (6568804353-1+2*2^10*c.k,111678228754624+c.lower,111678615888872+c.upper)) = pointBounds50086 := by
 decide +kernel
def cuts50087 : List PrefixCut := [⟨64,247881257,247881400⟩]
theorem checked50087 : checkPrefixCuts (2^48) 6568935425 10 Manual.Count131072.C050087.packed 64 cuts50087 = true := by
 decide +kernel
def cuts50088 : List PrefixCut := [⟨36,141356537,141356618⟩,
⟨64,249933047,249933187⟩]
theorem checked50088 : checkPrefixCuts (2^48) 6569066497 10 Manual.Count131072.C050088.packed 64 cuts50088 = true := by
 decide +kernel
def pointBounds50088 : List (Nat × Nat × Nat) := [(6569140224,111678866007171,111679253141780)]
theorem point_links_checked50088 : (cuts50088.take 1).map (fun c => (6569066497-1+2*2^10*c.k,111678724650634+c.lower,111679111785162+c.upper)) = pointBounds50088 := by
 decide +kernel
def cuts50089 : List PrefixCut := [⟨64,246114648,246114792⟩]
theorem checked50089 : checkPrefixCuts (2^48) 6569197569 10 Manual.Count131072.C050089.packed 64 cuts50089 = true := by
 decide +kernel
def cuts50090 : List PrefixCut := [⟨9,35905593,35905612⟩,
⟨64,249451755,249451896⟩]
theorem checked50090 : checkPrefixCuts (2^48) 6569328641 10 Manual.Count131072.C050090.packed 64 cuts50090 = true := by
 decide +kernel
def pointBounds50090 : List (Nat × Nat × Nat) := [(6569347072,111679256603922,111679643738753)]
theorem point_links_checked50090 : (cuts50090.take 1).map (fun c => (6569328641-1+2*2^10*c.k,111679220698329+c.lower,111679607833141+c.upper)) = pointBounds50090 := by
 decide +kernel
def cuts50091 : List PrefixCut := [⟨46,179180578,179180682⟩,
⟨64,248761244,248761388⟩]
theorem checked50091 : checkPrefixCuts (2^48) 6569459713 10 Manual.Count131072.C050091.packed 64 cuts50091 = true := by
 decide +kernel
def pointBounds50091 : List (Nat × Nat × Nat) := [(6569553920,111679649330662,111680036465719)]
theorem point_links_checked50091 : (cuts50091.take 1).map (fun c => (6569459713-1+2*2^10*c.k,111679470150084+c.lower,111679857285037+c.upper)) = pointBounds50091 := by
 decide +kernel
def cuts50092 : List PrefixCut := [⟨64,246314125,246314265⟩]
theorem checked50092 : checkPrefixCuts (2^48) 6569590785 10 Manual.Count131072.C050092.packed 64 cuts50092 = true := by
 decide +kernel
def cuts50093 : List PrefixCut := [⟨19,75619902,75619943⟩,
⟨64,254021109,254021252⟩]
theorem checked50093 : checkPrefixCuts (2^48) 6569721857 10 Manual.Count131072.C050093.packed 64 cuts50093 = true := by
 decide +kernel
def pointBounds50093 : List (Nat × Nat × Nat) := [(6569760768,111680040845355,111680427980633)]
theorem point_links_checked50093 : (cuts50093.take 1).map (fun c => (6569721857-1+2*2^10*c.k,111679965225453+c.lower,111680352360690+c.upper)) = pointBounds50093 := by
 decide +kernel
def cuts50094 : List PrefixCut := [⟨56,216742926,216743045⟩,
⟨64,246818435,246818572⟩]
theorem checked50094 : checkPrefixCuts (2^48) 6569852929 10 Manual.Count131072.C050094.packed 64 cuts50094 = true := by
 decide +kernel
def pointBounds50094 : List (Nat × Nat × Nat) := [(6569967616,111680435989488,111680823124987)]
theorem point_links_checked50094 : (cuts50094.take 1).map (fun c => (6569852929-1+2*2^10*c.k,111680219246562+c.lower,111680606381942+c.upper)) = pointBounds50094 := by
 decide +kernel
def cuts50095 : List PrefixCut := [⟨64,252811388,252811535⟩]
theorem checked50095 : checkPrefixCuts (2^48) 6569984001 10 Manual.Count131072.C050095.packed 64 cuts50095 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S6.B000002
