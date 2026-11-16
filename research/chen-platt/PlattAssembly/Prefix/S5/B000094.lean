import PlattAssemblyKernel
import PlattCertificates.Count131072.C043008
import PlattCertificates.Count131072.C043009
import PlattCertificates.Count131072.C043010
import PlattCertificates.Count131072.C043011
import PlattCertificates.Count131072.C043012
import PlattCertificates.Count131072.C043013
import PlattCertificates.Count131072.C043014
import PlattCertificates.Count131072.C043015
import PlattCertificates.Count131072.C043016
import PlattCertificates.Count131072.C043017
import PlattCertificates.Count131072.C043018
import PlattCertificates.Count131072.C043019
import PlattCertificates.Count131072.C043020
import PlattCertificates.Count131072.C043021
import PlattCertificates.Count131072.C043022
import PlattCertificates.Count131072.C043023
import PlattCertificates.Count131072.C043024
import PlattCertificates.Count131072.C043025
import PlattCertificates.Count131072.C043026
import PlattCertificates.Count131072.C043027
import PlattCertificates.Count131072.C043028
import PlattCertificates.Count131072.C043029
import PlattCertificates.Count131072.C043030
import PlattCertificates.Count131072.C043031
import PlattCertificates.Count131072.C043032
import PlattCertificates.Count131072.C043033
import PlattCertificates.Count131072.C043034
import PlattCertificates.Count131072.C043035
import PlattCertificates.Count131072.C043036
import PlattCertificates.Count131072.C043037
import PlattCertificates.Count131072.C043038
import PlattCertificates.Count131072.C043039
namespace ChenEffective.PlattWindow.Assembly.Prefix.S5.B000094
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts43008 : List PrefixCut := [⟨58,262008322,262008477⟩,
⟨64,289750644,289750816⟩]
theorem checked43008 : checkPrefixCuts (2^48) 5641076737 10 Manual.Count131072.C043008.packed 64 cuts43008 = true := by
 decide +kernel
def pointBounds43008 : List (Nat × Nat × Nat) := [(5641195520,109776260324878,109776646365789)]
theorem point_links_checked43008 : (cuts43008.take 1).map (fun c => (5641076737-1+2*2^10*c.k,109775998316556+c.lower,109776384357312+c.upper)) = pointBounds43008 := by
 decide +kernel
def cuts43009 : List PrefixCut := [⟨64,290242897,290243062⟩]
theorem checked43009 : checkPrefixCuts (2^48) 5641207809 10 Manual.Count131072.C043009.packed 64 cuts43009 = true := by
 decide +kernel
def cuts43010 : List PrefixCut := [⟨17,77935830,77935876⟩,
⟨64,294576961,294577135⟩]
theorem checked43010 : checkPrefixCuts (2^48) 5641338881 10 Manual.Count131072.C043010.packed 64 cuts43010 = true := by
 decide +kernel
def pointBounds43010 : List (Nat × Nat × Nat) := [(5641373696,109776656245927,109777042287066)]
theorem point_links_checked43010 : (cuts43010.take 1).map (fun c => (5641338881-1+2*2^10*c.k,109776578310097+c.lower,109776964351190+c.upper)) = pointBounds43010 := by
 decide +kernel
def cuts43011 : List PrefixCut := [⟨40,183857659,183857766⟩,
⟨64,294719794,294719966⟩]
theorem checked43011 : checkPrefixCuts (2^48) 5641469953 10 Manual.Count131072.C043011.packed 64 cuts43011 = true := by
 decide +kernel
def pointBounds43011 : List (Nat × Nat × Nat) := [(5641551872,109777056744717,109777442786091)]
theorem point_links_checked43011 : (cuts43011.take 1).map (fun c => (5641469953-1+2*2^10*c.k,109776872887058+c.lower,109777258928325+c.upper)) = pointBounds43011 := by
 decide +kernel
def cuts43012 : List PrefixCut := [⟨63,288775834,288776003⟩,
⟨64,293266076,293266248⟩]
theorem checked43012 : checkPrefixCuts (2^48) 5641601025 10 Manual.Count131072.C043012.packed 64 cuts43012 = true := by
 decide +kernel
def pointBounds43012 : List (Nat × Nat × Nat) := [(5641730048,109777456382686,109777842424294)]
theorem point_links_checked43012 : (cuts43012.take 1).map (fun c => (5641601025-1+2*2^10*c.k,109777167606852+c.lower,109777553648291+c.upper)) = pointBounds43012 := by
 decide +kernel
def cuts43013 : List PrefixCut := [⟨64,289866678,289866850⟩]
theorem checked43013 : checkPrefixCuts (2^48) 5641732097 10 Manual.Count131072.C043013.packed 64 cuts43013 = true := by
 decide +kernel
def cuts43014 : List PrefixCut := [⟨22,102574289,102574345⟩,
⟨64,290957553,290957720⟩]
theorem checked43014 : checkPrefixCuts (2^48) 5641863169 10 Manual.Count131072.C043014.packed 64 cuts43014 = true := by
 decide +kernel
def pointBounds43014 : List (Nat × Nat × Nat) := [(5641908224,109777853313895,109778239355734)]
theorem point_links_checked43014 : (cuts43014.take 1).map (fun c => (5641863169-1+2*2^10*c.k,109777750739606+c.lower,109778136781389+c.upper)) = pointBounds43014 := by
 decide +kernel
def cuts43015 : List PrefixCut := [⟨45,200902394,200902507⟩,
⟨64,286959661,286959822⟩]
theorem checked43015 : checkPrefixCuts (2^48) 5641994241 10 Manual.Count131072.C043015.packed 64 cuts43015 = true := by
 decide +kernel
def pointBounds43015 : List (Nat × Nat × Nat) := [(5642086400,109778242599553,109778628641616)]
theorem point_links_checked43015 : (cuts43015.take 1).map (fun c => (5641994241-1+2*2^10*c.k,109778041697159+c.lower,109778427739109+c.upper)) = pointBounds43015 := by
 decide +kernel
def cuts43016 : List PrefixCut := [⟨64,290794356,290794527⟩]
theorem checked43016 : checkPrefixCuts (2^48) 5642125313 10 Manual.Count131072.C043016.packed 64 cuts43016 = true := by
 decide +kernel
def cuts43017 : List PrefixCut := [⟨4,17759737,17759747⟩,
⟨64,290687805,290687981⟩]
theorem checked43017 : checkPrefixCuts (2^48) 5642256385 10 Manual.Count131072.C043017.packed 64 cuts43017 = true := by
 decide +kernel
def pointBounds43017 : List (Nat × Nat × Nat) := [(5642264576,109778637210913,109779023253205)]
theorem point_links_checked43017 : (cuts43017.take 1).map (fun c => (5642256385-1+2*2^10*c.k,109778619451176+c.lower,109779005493458+c.upper)) = pointBounds43017 := by
 decide +kernel
def cuts43018 : List PrefixCut := [⟨27,122618655,122618727⟩,
⟨64,288486127,288486296⟩]
theorem checked43018 : checkPrefixCuts (2^48) 5642387457 10 Manual.Count131072.C043018.packed 64 cuts43018 = true := by
 decide +kernel
def pointBounds43018 : List (Nat × Nat × Nat) := [(5642442752,109779032757636,109779418800166)]
theorem point_links_checked43018 : (cuts43018.take 1).map (fun c => (5642387457-1+2*2^10*c.k,109778910138981+c.lower,109779296181439+c.upper)) = pointBounds43018 := by
 decide +kernel
def cuts43019 : List PrefixCut := [⟨50,227322154,227322280⟩,
⟨64,290973618,290973779⟩]
theorem checked43019 : checkPrefixCuts (2^48) 5642518529 10 Manual.Count131072.C043019.packed 64 cuts43019 = true := by
 decide +kernel
def pointBounds43019 : List (Nat × Nat × Nat) := [(5642620928,109779425947262,109779811990015)]
theorem point_links_checked43019 : (cuts43019.take 1).map (fun c => (5642518529-1+2*2^10*c.k,109779198625108+c.lower,109779584667735+c.upper)) = pointBounds43019 := by
 decide +kernel
def cuts43020 : List PrefixCut := [⟨64,294259107,294259275⟩]
theorem checked43020 : checkPrefixCuts (2^48) 5642649601 10 Manual.Count131072.C043020.packed 64 cuts43020 = true := by
 decide +kernel
def cuts43021 : List PrefixCut := [⟨9,42998476,42998500⟩,
⟨64,291957719,291957889⟩]
theorem checked43021 : checkPrefixCuts (2^48) 5642780673 10 Manual.Count131072.C043021.packed 64 cuts43021 = true := by
 decide +kernel
def pointBounds43021 : List (Nat × Nat × Nat) := [(5642799104,109779826856309,109780212899289)]
theorem point_links_checked43021 : (cuts43021.take 1).map (fun c => (5642780673-1+2*2^10*c.k,109779783857833+c.lower,109780169900789+c.upper)) = pointBounds43021 := by
 decide +kernel
def cuts43022 : List PrefixCut := [⟨32,144704358,144704443⟩,
⟨64,289556666,289556834⟩]
theorem checked43022 : checkPrefixCuts (2^48) 5642911745 10 Manual.Count131072.C043022.packed 64 cuts43022 = true := by
 decide +kernel
def pointBounds43022 : List (Nat × Nat × Nat) := [(5642977280,109780220519910,109780606563121)]
theorem point_links_checked43022 : (cuts43022.take 1).map (fun c => (5642911745-1+2*2^10*c.k,109780075815552+c.lower,109780461858678+c.upper)) = pointBounds43022 := by
 decide +kernel
def cuts43023 : List PrefixCut := [⟨55,249098147,249098292⟩,
⟨64,291245823,291245994⟩]
theorem checked43023 : checkPrefixCuts (2^48) 5643042817 10 Manual.Count131072.C043023.packed 64 cuts43023 = true := by
 decide +kernel
def pointBounds43023 : List (Nat × Nat × Nat) := [(5643155456,109780614470365,109781000513804)]
theorem point_links_checked43023 : (cuts43023.take 1).map (fun c => (5643042817-1+2*2^10*c.k,109780365372218+c.lower,109780751415512+c.upper)) = pointBounds43023 := by
 decide +kernel
def cuts43024 : List PrefixCut := [⟨64,288495805,288495971⟩]
theorem checked43024 : checkPrefixCuts (2^48) 5643173889 10 Manual.Count131072.C043024.packed 64 cuts43024 = true := by
 decide +kernel
def cuts43025 : List PrefixCut := [⟨14,63893131,63893167⟩,
⟨64,290085172,290085336⟩]
theorem checked43025 : checkPrefixCuts (2^48) 5643304961 10 Manual.Count131072.C043025.packed 64 cuts43025 = true := by
 decide +kernel
def pointBounds43025 : List (Nat × Nat × Nat) := [(5643333632,109781009006977,109781395050644)]
theorem point_links_checked43025 : (cuts43025.take 1).map (fun c => (5643304961-1+2*2^10*c.k,109780945113846+c.lower,109781331157477+c.upper)) = pointBounds43025 := by
 decide +kernel
def cuts43026 : List PrefixCut := [⟨37,168381975,168382079⟩,
⟨64,294617116,294617293⟩]
theorem checked43026 : checkPrefixCuts (2^48) 5643436033 10 Manual.Count131072.C043026.packed 64 cuts43026 = true := by
 decide +kernel
def pointBounds43026 : List (Nat × Nat × Nat) := [(5643511808,109781403580993,109781789624892)]
theorem point_links_checked43026 : (cuts43026.take 1).map (fun c => (5643436033-1+2*2^10*c.k,109781235199018+c.lower,109781621242813+c.upper)) = pointBounds43026 := by
 decide +kernel
def cuts43027 : List PrefixCut := [⟨60,278151801,278151965⟩,
⟨64,297552876,297553052⟩]
theorem checked43027 : checkPrefixCuts (2^48) 5643567105 10 Manual.Count131072.C043027.packed 64 cuts43027 = true := by
 decide +kernel
def pointBounds43027 : List (Nat × Nat × Nat) := [(5643689984,109781807967935,109782194012071)]
theorem point_links_checked43027 : (cuts43027.take 1).map (fun c => (5643567105-1+2*2^10*c.k,109781529816134+c.lower,109781915860106+c.upper)) = pointBounds43027 := by
 decide +kernel
def cuts43028 : List PrefixCut := [⟨64,293755590,293755760⟩]
theorem checked43028 : checkPrefixCuts (2^48) 5643698177 10 Manual.Count131072.C043028.packed 64 cuts43028 = true := by
 decide +kernel
def cuts43029 : List PrefixCut := [⟨19,86329928,86329979⟩,
⟨64,293998127,293998295⟩]
theorem checked43029 : checkPrefixCuts (2^48) 5643829249 10 Manual.Count131072.C043029.packed 64 cuts43029 = true := by
 decide +kernel
def pointBounds43029 : List (Nat × Nat × Nat) := [(5643868160,109782207454528,109782593498897)]
theorem point_links_checked43029 : (cuts43029.take 1).map (fun c => (5643829249-1+2*2^10*c.k,109782121124600+c.lower,109782507168918+c.upper)) = pointBounds43029 := by
 decide +kernel
def cuts43030 : List PrefixCut := [⟨42,189761073,189761189⟩,
⟨64,291647365,291647540⟩]
theorem checked43030 : checkPrefixCuts (2^48) 5643960321 10 Manual.Count131072.C043030.packed 64 cuts43030 = true := by
 decide +kernel
def pointBounds43030 : List (Nat × Nat × Nat) := [(5644046336,109782604883800,109782990928402)]
theorem point_links_checked43030 : (cuts43030.take 1).map (fun c => (5643960321-1+2*2^10*c.k,109782415122727+c.lower,109782801167213+c.upper)) = pointBounds43030 := by
 decide +kernel
def cuts43031 : List PrefixCut := [⟨64,296876923,296877098⟩]
theorem checked43031 : checkPrefixCuts (2^48) 5644091393 10 Manual.Count131072.C043031.packed 64 cuts43031 = true := by
 decide +kernel
def cuts43032 : List PrefixCut := [⟨1,4787477,4787480⟩,
⟨64,288192840,288193013⟩]
theorem checked43032 : checkPrefixCuts (2^48) 5644222465 10 Manual.Count131072.C043032.packed 64 cuts43032 = true := by
 decide +kernel
def pointBounds43032 : List (Nat × Nat × Nat) := [(5644224512,109783008434492,109783394479331)]
theorem point_links_checked43032 : (cuts43032.take 1).map (fun c => (5644222465-1+2*2^10*c.k,109783003647015+c.lower,109783389691851+c.upper)) = pointBounds43032 := by
 decide +kernel
def cuts43033 : List PrefixCut := [⟨24,108961987,108962051⟩,
⟨64,290529936,290530110⟩]
theorem checked43033 : checkPrefixCuts (2^48) 5644353537 10 Manual.Count131072.C043033.packed 64 cuts43033 = true := by
 decide +kernel
def pointBounds43033 : List (Nat × Nat × Nat) := [(5644402688,109783400801842,109783786846915)]
theorem point_links_checked43033 : (cuts43033.take 1).map (fun c => (5644353537-1+2*2^10*c.k,109783291839855+c.lower,109783677884864+c.upper)) = pointBounds43033 := by
 decide +kernel
def cuts43034 : List PrefixCut := [⟨47,212582248,212582367⟩,
⟨64,289825055,289825219⟩]
theorem checked43034 : checkPrefixCuts (2^48) 5644484609 10 Manual.Count131072.C043034.packed 64 cuts43034 = true := by
 decide +kernel
def pointBounds43034 : List (Nat × Nat × Nat) := [(5644580864,109783794952039,109784180997341)]
theorem point_links_checked43034 : (cuts43034.take 1).map (fun c => (5644484609-1+2*2^10*c.k,109783582369791+c.lower,109783968414974+c.upper)) = pointBounds43034 := by
 decide +kernel
def cuts43035 : List PrefixCut := [⟨64,288222642,288222815⟩]
theorem checked43035 : checkPrefixCuts (2^48) 5644615681 10 Manual.Count131072.C043035.packed 64 cuts43035 = true := by
 decide +kernel
def cuts43036 : List PrefixCut := [⟨6,27176356,27176373⟩,
⟨64,293102650,293102813⟩]
theorem checked43036 : checkPrefixCuts (2^48) 5644746753 10 Manual.Count131072.C043036.packed 64 cuts43036 = true := by
 decide +kernel
def pointBounds43036 : List (Nat × Nat × Nat) := [(5644759040,109784187593844,109784573639381)]
theorem point_links_checked43036 : (cuts43036.take 1).map (fun c => (5644746753-1+2*2^10*c.k,109784160417488+c.lower,109784546463008+c.upper)) = pointBounds43036 := by
 decide +kernel
def cuts43037 : List PrefixCut := [⟨29,132886248,132886325⟩,
⟨64,291250911,291251083⟩]
theorem checked43037 : checkPrefixCuts (2^48) 5644877825 10 Manual.Count131072.C043037.packed 64 cuts43037 = true := by
 decide +kernel
def pointBounds43037 : List (Nat × Nat × Nat) := [(5644937216,109784586406386,109784972452146)]
theorem point_links_checked43037 : (cuts43037.take 1).map (fun c => (5644877825-1+2*2^10*c.k,109784453520138+c.lower,109784839565821+c.upper)) = pointBounds43037 := by
 decide +kernel
def cuts43038 : List PrefixCut := [⟨52,237593102,237593242⟩,
⟨64,291294007,291294180⟩]
theorem checked43038 : checkPrefixCuts (2^48) 5645008897 10 Manual.Count131072.C043038.packed 64 cuts43038 = true := by
 decide +kernel
def pointBounds43038 : List (Nat × Nat × Nat) := [(5645115392,109784982364151,109785368410146)]
theorem point_links_checked43038 : (cuts43038.take 1).map (fun c => (5645008897-1+2*2^10*c.k,109784744771049+c.lower,109785130816904+c.upper)) = pointBounds43038 := by
 decide +kernel
def cuts43039 : List PrefixCut := [⟨64,292434072,292434241⟩]
theorem checked43039 : checkPrefixCuts (2^48) 5645139969 10 Manual.Count131072.C043039.packed 64 cuts43039 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S5.B000094
