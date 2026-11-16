import PlattAssemblyKernel
import PlattCertificates.Count131072.C042944
import PlattCertificates.Count131072.C042945
import PlattCertificates.Count131072.C042946
import PlattCertificates.Count131072.C042947
import PlattCertificates.Count131072.C042948
import PlattCertificates.Count131072.C042949
import PlattCertificates.Count131072.C042950
import PlattCertificates.Count131072.C042951
import PlattCertificates.Count131072.C042952
import PlattCertificates.Count131072.C042953
import PlattCertificates.Count131072.C042954
import PlattCertificates.Count131072.C042955
import PlattCertificates.Count131072.C042956
import PlattCertificates.Count131072.C042957
import PlattCertificates.Count131072.C042958
import PlattCertificates.Count131072.C042959
import PlattCertificates.Count131072.C042960
import PlattCertificates.Count131072.C042961
import PlattCertificates.Count131072.C042962
import PlattCertificates.Count131072.C042963
import PlattCertificates.Count131072.C042964
import PlattCertificates.Count131072.C042965
import PlattCertificates.Count131072.C042966
import PlattCertificates.Count131072.C042967
import PlattCertificates.Count131072.C042968
import PlattCertificates.Count131072.C042969
import PlattCertificates.Count131072.C042970
import PlattCertificates.Count131072.C042971
import PlattCertificates.Count131072.C042972
import PlattCertificates.Count131072.C042973
import PlattCertificates.Count131072.C042974
import PlattCertificates.Count131072.C042975
namespace ChenEffective.PlattWindow.Assembly.Prefix.S5.B000092
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts42944 : List PrefixCut := [⟨64,289582518,289582689⟩]
theorem checked42944 : checkPrefixCuts (2^48) 5632688129 10 Manual.Count131072.C042944.packed 64 cuts42944 = true := by
 decide +kernel
def cuts42945 : List PrefixCut := [⟨20,91795509,91795562⟩,
⟨64,293673317,293673494⟩]
theorem checked42945 : checkPrefixCuts (2^48) 5632819201 10 Manual.Count131072.C042945.packed 64 cuts42945 = true := by
 decide +kernel
def pointBounds42945 : List (Nat × Nat × Nat) := [(5632860160,109757712180503,109758098210611)]
theorem point_links_checked42945 : (cuts42945.take 1).map (fun c => (5632819201-1+2*2^10*c.k,109757620384994+c.lower,109758006415049+c.upper)) = pointBounds42945 := by
 decide +kernel
def cuts42946 : List PrefixCut := [⟨42,192430527,192430644⟩,
⟨64,292067497,292067674⟩]
theorem checked42946 : checkPrefixCuts (2^48) 5632950273 10 Manual.Count131072.C042946.packed 64 cuts42946 = true := by
 decide +kernel
def pointBounds42946 : List (Nat × Nat × Nat) := [(5633036288,109758106488838,109758492519187)]
theorem point_links_checked42946 : (cuts42946.take 1).map (fun c => (5632950273-1+2*2^10*c.k,109757914058311+c.lower,109758300088543+c.upper)) = pointBounds42946 := by
 decide +kernel
def cuts42947 : List PrefixCut := [⟨64,296307912,296308088⟩]
theorem checked42947 : checkPrefixCuts (2^48) 5633081345 10 Manual.Count131072.C042947.packed 64 cuts42947 = true := by
 decide +kernel
def pointBounds42947 : List (Nat × Nat × Nat) := [(5633212416,109758502433720,109758888464305)]
theorem point_links_checked42947 : (cuts42947.take 1).map (fun c => (5633081345-1+2*2^10*c.k,109758206125808+c.lower,109758592156217+c.upper)) = pointBounds42947 := by
 decide +kernel
def cuts42948 : List PrefixCut := [⟨64,289405657,289405827⟩]
theorem checked42948 : checkPrefixCuts (2^48) 5633212417 10 Manual.Count131072.C042948.packed 64 cuts42948 = true := by
 decide +kernel
def cuts42949 : List PrefixCut := [⟨22,99631538,99631595⟩,
⟨64,292446800,292446969⟩]
theorem checked42949 : checkPrefixCuts (2^48) 5633343489 10 Manual.Count131072.C042949.packed 64 cuts42949 = true := by
 decide +kernel
def pointBounds42949 : List (Nat × Nat × Nat) := [(5633388544,109758891470915,109759277501727)]
theorem point_links_checked42949 : (cuts42949.take 1).map (fun c => (5633343489-1+2*2^10*c.k,109758791839377+c.lower,109759177870132+c.upper)) = pointBounds42949 := by
 decide +kernel
def cuts42950 : List PrefixCut := [⟨44,198158425,198158539⟩,
⟨64,291790448,291790615⟩]
theorem checked42950 : checkPrefixCuts (2^48) 5633474561 10 Manual.Count131072.C042950.packed 64 cuts42950 = true := by
 decide +kernel
def pointBounds42950 : List (Nat × Nat × Nat) := [(5633564672,109759282444602,109759668475640)]
theorem point_links_checked42950 : (cuts42950.take 1).map (fun c => (5633474561-1+2*2^10*c.k,109759084286177+c.lower,109759470317101+c.upper)) = pointBounds42950 := by
 decide +kernel
def cuts42951 : List PrefixCut := [⟨64,291334064,291334230⟩]
theorem checked42951 : checkPrefixCuts (2^48) 5633605633 10 Manual.Count131072.C042951.packed 64 cuts42951 = true := by
 decide +kernel
def cuts42952 : List PrefixCut := [⟨2,9292999,9293005⟩,
⟨64,290078218,290078390⟩]
theorem checked42952 : checkPrefixCuts (2^48) 5633736705 10 Manual.Count131072.C042952.packed 64 cuts42952 = true := by
 decide +kernel
def pointBounds42952 : List (Nat × Nat × Nat) := [(5633740800,109759676703688,109760062734951)]
theorem point_links_checked42952 : (cuts42952.take 1).map (fun c => (5633736705-1+2*2^10*c.k,109759667410689+c.lower,109760053441946+c.upper)) = pointBounds42952 := by
 decide +kernel
def cuts42953 : List PrefixCut := [⟨24,107715912,107715974⟩,
⟨64,288672549,288672715⟩]
theorem checked42953 : checkPrefixCuts (2^48) 5633867777 10 Manual.Count131072.C042953.packed 64 cuts42953 = true := by
 decide +kernel
def pointBounds42953 : List (Nat × Nat × Nat) := [(5633916928,109760065204819,109760451236310)]
theorem point_links_checked42953 : (cuts42953.take 1).map (fun c => (5633867777-1+2*2^10*c.k,109759957488907+c.lower,109760343520336+c.upper)) = pointBounds42953 := by
 decide +kernel
def cuts42954 : List PrefixCut := [⟨46,211928782,211928909⟩,
⟨64,294261304,294261479⟩]
theorem checked42954 : checkPrefixCuts (2^48) 5633998849 10 Manual.Count131072.C042954.packed 64 cuts42954 = true := by
 decide +kernel
def pointBounds42954 : List (Nat × Nat × Nat) := [(5634093056,109760458090238,109760844121960)]
theorem point_links_checked42954 : (cuts42954.take 1).map (fun c => (5633998849-1+2*2^10*c.k,109760246161456+c.lower,109760632193051+c.upper)) = pointBounds42954 := by
 decide +kernel
def cuts42955 : List PrefixCut := [⟨64,290607489,290607661⟩]
theorem checked42955 : checkPrefixCuts (2^48) 5634129921 10 Manual.Count131072.C042955.packed 64 cuts42955 = true := by
 decide +kernel
def cuts42956 : List PrefixCut := [⟨4,18784093,18784105⟩,
⟨64,290301016,290301185⟩]
theorem checked42956 : checkPrefixCuts (2^48) 5634260993 10 Manual.Count131072.C042956.packed 64 cuts42956 = true := by
 decide +kernel
def pointBounds42956 : List (Nat × Nat × Nat) := [(5634269184,109760849814342,109761235846296)]
theorem point_links_checked42956 : (cuts42956.take 1).map (fun c => (5634260993-1+2*2^10*c.k,109760831030249+c.lower,109761217062191+c.upper)) = pointBounds42956 := by
 decide +kernel
def cuts42957 : List PrefixCut := [⟨26,118296600,118296667⟩,
⟨64,293291599,293291768⟩]
theorem checked42957 : checkPrefixCuts (2^48) 5634392065 10 Manual.Count131072.C042957.packed 64 cuts42957 = true := by
 decide +kernel
def pointBounds42957 : List (Nat × Nat × Nat) := [(5634445312,109761239627865,109761625660043)]
theorem point_links_checked42957 : (cuts42957.take 1).map (fun c => (5634392065-1+2*2^10*c.k,109761121331265+c.lower,109761507363376+c.upper)) = pointBounds42957 := by
 decide +kernel
def cuts42958 : List PrefixCut := [⟨48,220751017,220751142⟩,
⟨64,294483695,294483862⟩]
theorem checked42958 : checkPrefixCuts (2^48) 5634523137 10 Manual.Count131072.C042958.packed 64 cuts42958 = true := by
 decide +kernel
def pointBounds42958 : List (Nat × Nat × Nat) := [(5634621440,109761635373881,109762021406286)]
theorem point_links_checked42958 : (cuts42958.take 1).map (fun c => (5634523137-1+2*2^10*c.k,109761414622864+c.lower,109761800655144+c.upper)) = pointBounds42958 := by
 decide +kernel
def cuts42959 : List PrefixCut := [⟨64,294326960,294327130⟩]
theorem checked42959 : checkPrefixCuts (2^48) 5634654209 10 Manual.Count131072.C042959.packed 64 cuts42959 = true := by
 decide +kernel
def cuts42960 : List PrefixCut := [⟨6,27174446,27174464⟩,
⟨64,292771612,292771778⟩]
theorem checked42960 : checkPrefixCuts (2^48) 5634785281 10 Manual.Count131072.C042960.packed 64 cuts42960 = true := by
 decide +kernel
def pointBounds42960 : List (Nat × Nat × Nat) := [(5634797568,109762030607965,109762416640600)]
theorem point_links_checked42960 : (cuts42960.take 1).map (fun c => (5634785281-1+2*2^10*c.k,109762003433519+c.lower,109762389466136+c.upper)) = pointBounds42960 := by
 decide +kernel
def cuts42961 : List PrefixCut := [⟨28,125078976,125079047⟩,
⟨64,290616874,290617041⟩]
theorem checked42961 : checkPrefixCuts (2^48) 5634916353 10 Manual.Count131072.C042961.packed 64 cuts42961 = true := by
 decide +kernel
def pointBounds42961 : List (Nat × Nat × Nat) := [(5634973696,109762421284107,109762807316961)]
theorem point_links_checked42961 : (cuts42961.take 1).map (fun c => (5634916353-1+2*2^10*c.k,109762296205131+c.lower,109762682237914+c.upper)) = pointBounds42961 := by
 decide +kernel
def cuts42962 : List PrefixCut := [⟨50,229621536,229621670⟩,
⟨64,293007735,293007907⟩]
theorem checked42962 : checkPrefixCuts (2^48) 5635047425 10 Manual.Count131072.C042962.packed 64 cuts42962 = true := by
 decide +kernel
def pointBounds42962 : List (Nat × Nat × Nat) := [(5635149824,109762816443541,109763202476625)]
theorem point_links_checked42962 : (cuts42962.take 1).map (fun c => (5635047425-1+2*2^10*c.k,109762586822005+c.lower,109762972854955+c.upper)) = pointBounds42962 := by
 decide +kernel
def cuts42963 : List PrefixCut := [⟨64,292251669,292251846⟩]
theorem checked42963 : checkPrefixCuts (2^48) 5635178497 10 Manual.Count131072.C042963.packed 64 cuts42963 = true := by
 decide +kernel
def cuts42964 : List PrefixCut := [⟨8,35962821,35962842⟩,
⟨64,291545586,291545759⟩]
theorem checked42964 : checkPrefixCuts (2^48) 5635309569 10 Manual.Count131072.C042964.packed 64 cuts42964 = true := by
 decide +kernel
def pointBounds42964 : List (Nat × Nat × Nat) := [(5635325952,109763208044230,109763594077550)]
theorem point_links_checked42964 : (cuts42964.take 1).map (fun c => (5635309569-1+2*2^10*c.k,109763172081409+c.lower,109763558114708+c.upper)) = pointBounds42964 := by
 decide +kernel
def cuts42965 : List PrefixCut := [⟨30,135905789,135905869⟩,
⟨64,288941624,288941791⟩]
theorem checked42965 : checkPrefixCuts (2^48) 5635440641 10 Manual.Count131072.C042965.packed 64 cuts42965 = true := by
 decide +kernel
def pointBounds42965 : List (Nat × Nat × Nat) := [(5635502080,109763599532784,109763985566336)]
theorem point_links_checked42965 : (cuts42965.take 1).map (fun c => (5635440641-1+2*2^10*c.k,109763463626995+c.lower,109763849660467+c.upper)) = pointBounds42965 := by
 decide +kernel
def cuts42966 : List PrefixCut := [⟨52,234644599,234644743⟩,
⟨64,288934879,288935055⟩]
theorem checked42966 : checkPrefixCuts (2^48) 5635571713 10 Manual.Count131072.C042966.packed 64 cuts42966 = true := by
 decide +kernel
def pointBounds42966 : List (Nat × Nat × Nat) := [(5635678208,109763987213218,109764373247001)]
theorem point_links_checked42966 : (cuts42966.take 1).map (fun c => (5635571713-1+2*2^10*c.k,109763752568619+c.lower,109764138602258+c.upper)) = pointBounds42966 := by
 decide +kernel
def cuts42967 : List PrefixCut := [⟨64,292024726,292024895⟩]
theorem checked42967 : checkPrefixCuts (2^48) 5635702785 10 Manual.Count131072.C042967.packed 64 cuts42967 = true := by
 decide +kernel
def cuts42968 : List PrefixCut := [⟨10,46897134,46897162⟩,
⟨64,293416342,293416515⟩]
theorem checked42968 : checkPrefixCuts (2^48) 5635833857 10 Manual.Count131072.C042968.packed 64 cuts42968 = true := by
 decide +kernel
def pointBounds42968 : List (Nat × Nat × Nat) := [(5635854336,109764380425358,109764766459370)]
theorem point_links_checked42968 : (cuts42968.take 1).map (fun c => (5635833857-1+2*2^10*c.k,109764333528224+c.lower,109764719562208+c.upper)) = pointBounds42968 := by
 decide +kernel
def cuts42969 : List PrefixCut := [⟨32,146730591,146730677⟩,
⟨64,290163317,290163488⟩]
theorem checked42969 : checkPrefixCuts (2^48) 5635964929 10 Manual.Count131072.C042969.packed 64 cuts42969 = true := by
 decide +kernel
def pointBounds42969 : List (Nat × Nat × Nat) := [(5636030464,109764773675157,109765159709400)]
theorem point_links_checked42969 : (cuts42969.take 1).map (fun c => (5635964929-1+2*2^10*c.k,109764626944566+c.lower,109765012978723+c.upper)) = pointBounds42969 := by
 decide +kernel
def cuts42970 : List PrefixCut := [⟨54,247357652,247357794⟩,
⟨64,293702340,293702511⟩]
theorem checked42970 : checkPrefixCuts (2^48) 5636096001 10 Manual.Count131072.C042970.packed 64 cuts42970 = true := by
 decide +kernel
def pointBounds42970 : List (Nat × Nat × Nat) := [(5636206592,109765164465535,109765550500005)]
theorem point_links_checked42970 : (cuts42970.take 1).map (fun c => (5636096001-1+2*2^10*c.k,109764917107883+c.lower,109765303142211+c.upper)) = pointBounds42970 := by
 decide +kernel
def cuts42971 : List PrefixCut := [⟨64,290948831,290948998⟩]
theorem checked42971 : checkPrefixCuts (2^48) 5636227073 10 Manual.Count131072.C042971.packed 64 cuts42971 = true := by
 decide +kernel
def cuts42972 : List PrefixCut := [⟨13,61724636,61724672⟩,
⟨64,292739881,292740052⟩]
theorem checked42972 : checkPrefixCuts (2^48) 5636358145 10 Manual.Count131072.C042972.packed 64 cuts42972 = true := by
 decide +kernel
def pointBounds42972 : List (Nat × Nat × Nat) := [(5636384768,109765563483690,109765949518392)]
theorem point_links_checked42972 : (cuts42972.take 1).map (fun c => (5636358145-1+2*2^10*c.k,109765501759054+c.lower,109765887793720+c.upper)) = pointBounds42972 := by
 decide +kernel
def cuts42973 : List PrefixCut := [⟨36,161448434,161448530⟩,
⟨64,289337297,289337467⟩]
theorem checked42973 : checkPrefixCuts (2^48) 5636489217 10 Manual.Count131072.C042973.packed 64 cuts42973 = true := by
 decide +kernel
def pointBounds42973 : List (Nat × Nat × Nat) := [(5636562944,109765955947369,109766341982302)]
theorem point_links_checked42973 : (cuts42973.take 1).map (fun c => (5636489217-1+2*2^10*c.k,109765794498935+c.lower,109766180533772+c.upper)) = pointBounds42973 := by
 decide +kernel
def cuts42974 : List PrefixCut := [⟨59,269855674,269855827⟩,
⟨64,293425326,293425493⟩]
theorem checked42974 : checkPrefixCuts (2^48) 5636620289 10 Manual.Count131072.C042974.packed 64 cuts42974 = true := by
 decide +kernel
def pointBounds42974 : List (Nat × Nat × Nat) := [(5636741120,109766353691906,109766739727066)]
theorem point_links_checked42974 : (cuts42974.take 1).map (fun c => (5636620289-1+2*2^10*c.k,109766083836232+c.lower,109766469871239+c.upper)) = pointBounds42974 := by
 decide +kernel
def cuts42975 : List PrefixCut := [⟨64,290971688,290971863⟩]
theorem checked42975 : checkPrefixCuts (2^48) 5636751361 10 Manual.Count131072.C042975.packed 64 cuts42975 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S5.B000092
