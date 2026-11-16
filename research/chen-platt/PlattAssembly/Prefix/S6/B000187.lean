import PlattAssemblyKernel
import PlattCertificates.Count131072.C055984
import PlattCertificates.Count131072.C055985
import PlattCertificates.Count131072.C055986
import PlattCertificates.Count131072.C055987
import PlattCertificates.Count131072.C055988
import PlattCertificates.Count131072.C055989
import PlattCertificates.Count131072.C055990
import PlattCertificates.Count131072.C055991
import PlattCertificates.Count131072.C055992
import PlattCertificates.Count131072.C055993
import PlattCertificates.Count131072.C055994
import PlattCertificates.Count131072.C055995
import PlattCertificates.Count131072.C055996
import PlattCertificates.Count131072.C055997
import PlattCertificates.Count131072.C055998
import PlattCertificates.Count131072.C055999
import PlattCertificates.Count131072.C056000
import PlattCertificates.Count131072.C056001
import PlattCertificates.Count131072.C056002
import PlattCertificates.Count131072.C056003
import PlattCertificates.Count131072.C056004
import PlattCertificates.Count131072.C056005
import PlattCertificates.Count131072.C056006
import PlattCertificates.Count131072.C056007
import PlattCertificates.Count131072.C056008
import PlattCertificates.Count131072.C056009
import PlattCertificates.Count131072.C056010
import PlattCertificates.Count131072.C056011
import PlattCertificates.Count131072.C056012
import PlattCertificates.Count131072.C056013
import PlattCertificates.Count131072.C056014
import PlattCertificates.Count131072.C056015
namespace ChenEffective.PlattWindow.Assembly.Prefix.S6.B000187
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts55984 : List PrefixCut := [⟨64,221171834,221171958⟩]
theorem checked55984 : checkPrefixCuts (2^48) 7341867009 10 Manual.Count131072.C055984.packed 64 cuts55984 = true := by
 decide +kernel
def cuts55985 : List PrefixCut := [⟨17,56931264,56931296⟩,
⟨64,220171113,220171239⟩]
theorem checked55985 : checkPrefixCuts (2^48) 7341998081 10 Manual.Count131072.C055985.packed 64 cuts55985 = true := by
 decide +kernel
def pointBounds55985 : List (Nat × Nat × Nat) := [(7342032896,113060474276584,113060862196109)]
theorem point_links_checked55985 : (cuts55985.take 1).map (fun c => (7341998081-1+2*2^10*c.k,113060417345320+c.lower,113060805264813+c.upper)) = pointBounds55985 := by
 decide +kernel
def cuts55986 : List PrefixCut := [⟨64,221547317,221547442⟩]
theorem checked55986 : checkPrefixCuts (2^48) 7342129153 10 Manual.Count131072.C055986.packed 64 cuts55986 = true := by
 decide +kernel
def cuts55987 : List PrefixCut := [⟨2,7053873,7053877⟩,
⟨64,219971581,219971707⟩]
theorem checked55987 : checkPrefixCuts (2^48) 7342260225 10 Manual.Count131072.C055987.packed 64 cuts55987 = true := by
 decide +kernel
def pointBounds55987 : List (Nat × Nat × Nat) := [(7342264320,113060866117623,113061254037371)]
theorem point_links_checked55987 : (cuts55987.take 1).map (fun c => (7342260225-1+2*2^10*c.k,113060859063750+c.lower,113061246983494+c.upper)) = pointBounds55987 := by
 decide +kernel
def cuts55988 : List PrefixCut := [⟨51,178144221,178144321⟩,
⟨64,223609505,223609629⟩]
theorem checked55988 : checkPrefixCuts (2^48) 7342391297 10 Manual.Count131072.C055988.packed 64 cuts55988 = true := by
 decide +kernel
def pointBounds55988 : List (Nat × Nat × Nat) := [(7342495744,113061257179552,113061645099522)]
theorem point_links_checked55988 : (cuts55988.take 1).map (fun c => (7342391297-1+2*2^10*c.k,113061079035331+c.lower,113061466955201+c.upper)) = pointBounds55988 := by
 decide +kernel
def cuts55989 : List PrefixCut := [⟨64,220347072,220347192⟩]
theorem checked55989 : checkPrefixCuts (2^48) 7342522369 10 Manual.Count131072.C055989.packed 64 cuts55989 = true := by
 decide +kernel
def cuts55990 : List PrefixCut := [⟨36,124010576,124010648⟩,
⟨64,221071468,221071594⟩]
theorem checked55990 : checkPrefixCuts (2^48) 7342653441 10 Manual.Count131072.C055990.packed 64 cuts55990 = true := by
 decide +kernel
def pointBounds55990 : List (Nat × Nat × Nat) := [(7342727168,113061647002484,113062034922670)]
theorem point_links_checked55990 : (cuts55990.take 1).map (fun c => (7342653441-1+2*2^10*c.k,113061522991908+c.lower,113061910912022+c.upper)) = pointBounds55990 := by
 decide +kernel
def cuts55991 : List PrefixCut := [⟨64,222370867,222370992⟩]
theorem checked55991 : checkPrefixCuts (2^48) 7342784513 10 Manual.Count131072.C055991.packed 64 cuts55991 = true := by
 decide +kernel
def cuts55992 : List PrefixCut := [⟨21,73483866,73483908⟩,
⟨64,221331934,221332060⟩]
theorem checked55992 : checkPrefixCuts (2^48) 7342915585 10 Manual.Count131072.C055992.packed 64 cuts55992 = true := by
 decide +kernel
def pointBounds55992 : List (Nat × Nat × Nat) := [(7342958592,113062039918109,113062427838516)]
theorem point_links_checked55992 : (cuts55992.take 1).map (fun c => (7342915585-1+2*2^10*c.k,113061966434243+c.lower,113062354354608+c.upper)) = pointBounds55992 := by
 decide +kernel
def cuts55993 : List PrefixCut := [⟨64,224279519,224279646⟩]
theorem checked55993 : checkPrefixCuts (2^48) 7343046657 10 Manual.Count131072.C055993.packed 64 cuts55993 = true := by
 decide +kernel
def cuts55994 : List PrefixCut := [⟨6,20660653,20660665⟩,
⟨64,220710720,220710843⟩]
theorem checked55994 : checkPrefixCuts (2^48) 7343177729 10 Manual.Count131072.C055994.packed 64 cuts55994 = true := by
 decide +kernel
def pointBounds55994 : List (Nat × Nat × Nat) := [(7343190016,113062432706349,113062820626979)]
theorem point_links_checked55994 : (cuts55994.take 1).map (fun c => (7343177729-1+2*2^10*c.k,113062412045696+c.lower,113062799966314+c.upper)) = pointBounds55994 := by
 decide +kernel
def cuts55995 : List PrefixCut := [⟨55,193185760,193185870⟩,
⟨64,223964880,223965008⟩]
theorem checked55995 : checkPrefixCuts (2^48) 7343308801 10 Manual.Count131072.C055995.packed 64 cuts55995 = true := by
 decide +kernel
def pointBounds55995 : List (Nat × Nat × Nat) := [(7343421440,113062825942176,113063213863027)]
theorem point_links_checked55995 : (cuts55995.take 1).map (fun c => (7343308801-1+2*2^10*c.k,113062632756416+c.lower,113063020677157+c.upper)) = pointBounds55995 := by
 decide +kernel
def cuts55996 : List PrefixCut := [⟨64,218863009,218863135⟩]
theorem checked55996 : checkPrefixCuts (2^48) 7343439873 10 Manual.Count131072.C055996.packed 64 cuts55996 = true := by
 decide +kernel
def cuts55997 : List PrefixCut := [⟨40,136950289,136950367⟩,
⟨64,221810417,221810542⟩]
theorem checked55997 : checkPrefixCuts (2^48) 7343570945 10 Manual.Count131072.C055997.packed 64 cuts55997 = true := by
 decide +kernel
def pointBounds55997 : List (Nat × Nat × Nat) := [(7343652864,113063212534594,113063600455667)]
theorem point_links_checked55997 : (cuts55997.take 1).map (fun c => (7343570945-1+2*2^10*c.k,113063075584305+c.lower,113063463505300+c.upper)) = pointBounds55997 := by
 decide +kernel
def cuts55998 : List PrefixCut := [⟨64,220043370,220043498⟩]
theorem checked55998 : checkPrefixCuts (2^48) 7343702017 10 Manual.Count131072.C055998.packed 64 cuts55998 = true := by
 decide +kernel
def cuts55999 : List PrefixCut := [⟨25,85126328,85126376⟩,
⟨64,219847795,219847922⟩]
theorem checked55999 : checkPrefixCuts (2^48) 7343833089 10 Manual.Count131072.C055999.packed 64 cuts55999 = true := by
 decide +kernel
def pointBounds55999 : List (Nat × Nat × Nat) := [(7343884288,113063602564420,113063990485716)]
theorem point_links_checked55999 : (cuts55999.take 1).map (fun c => (7343833089-1+2*2^10*c.k,113063517438092+c.lower,113063905359340+c.upper)) = pointBounds55999 := by
 decide +kernel
def cuts56000 : List PrefixCut := [⟨64,221721892,221722019⟩]
theorem checked56000 : checkPrefixCuts (2^48) 7343964161 10 Manual.Count131072.C056000.packed 64 cuts56000 = true := by
 decide +kernel
def cuts56001 : List PrefixCut := [⟨10,35260511,35260530⟩,
⟨64,222867738,222867863⟩]
theorem checked56001 : checkPrefixCuts (2^48) 7344095233 10 Manual.Count131072.C056001.packed 64 cuts56001 = true := by
 decide +kernel
def pointBounds56001 : List (Nat × Nat × Nat) := [(7344115712,113063994268290,113064382189811)]
theorem point_links_checked56001 : (cuts56001.take 1).map (fun c => (7344095233-1+2*2^10*c.k,113063959007779+c.lower,113064346929281+c.upper)) = pointBounds56001 := by
 decide +kernel
def cuts56002 : List PrefixCut := [⟨59,201708124,201708238⟩,
⟨64,219874342,219874466⟩]
theorem checked56002 : checkPrefixCuts (2^48) 7344226305 10 Manual.Count131072.C056002.packed 64 cuts56002 = true := by
 decide +kernel
def pointBounds56002 : List (Nat × Nat × Nat) := [(7344347136,113064383583641,113064771505382)]
theorem point_links_checked56002 : (cuts56002.take 1).map (fun c => (7344226305-1+2*2^10*c.k,113064181875517+c.lower,113064569797144+c.upper)) = pointBounds56002 := by
 decide +kernel
def cuts56003 : List PrefixCut := [⟨64,222208263,222208389⟩]
theorem checked56003 : checkPrefixCuts (2^48) 7344357377 10 Manual.Count131072.C056003.packed 64 cuts56003 = true := by
 decide +kernel
def cuts56004 : List PrefixCut := [⟨44,154409046,154409133⟩,
⟨64,224963651,224963778⟩]
theorem checked56004 : checkPrefixCuts (2^48) 7344488449 10 Manual.Count131072.C056004.packed 64 cuts56004 = true := by
 decide +kernel
def pointBounds56004 : List (Nat × Nat × Nat) := [(7344578560,113064778367168,113065166289132)]
theorem point_links_checked56004 : (cuts56004.take 1).map (fun c => (7344488449-1+2*2^10*c.k,113064623958122+c.lower,113065011879999+c.upper)) = pointBounds56004 := by
 decide +kernel
def cuts56005 : List PrefixCut := [⟨64,221702122,221702247⟩]
theorem checked56005 : checkPrefixCuts (2^48) 7344619521 10 Manual.Count131072.C056005.packed 64 cuts56005 = true := by
 decide +kernel
def cuts56006 : List PrefixCut := [⟨29,100866450,100866507⟩,
⟨64,220625133,220625258⟩]
theorem checked56006 : checkPrefixCuts (2^48) 7344750593 10 Manual.Count131072.C056006.packed 64 cuts56006 = true := by
 decide +kernel
def pointBounds56006 : List (Nat × Nat × Nat) := [(7344809984,113065171490345,113065559412531)]
theorem point_links_checked56006 : (cuts56006.take 1).map (fun c => (7344750593-1+2*2^10*c.k,113065070623895+c.lower,113065458546024+c.upper)) = pointBounds56006 := by
 decide +kernel
def cuts56007 : List PrefixCut := [⟨64,221885813,221885938⟩]
theorem checked56007 : checkPrefixCuts (2^48) 7344881665 10 Manual.Count131072.C056007.packed 64 cuts56007 = true := by
 decide +kernel
def cuts56008 : List PrefixCut := [⟨14,45602980,45603008⟩,
⟨64,220578894,220579020⟩]
theorem checked56008 : checkPrefixCuts (2^48) 7345012737 10 Manual.Count131072.C056008.packed 64 cuts56008 = true := by
 decide +kernel
def pointBounds56008 : List (Nat × Nat × Nat) := [(7345041408,113065558737821,113065946660228)]
theorem point_links_checked56008 : (cuts56008.take 1).map (fun c => (7345012737-1+2*2^10*c.k,113065513134841+c.lower,113065901057220+c.upper)) = pointBounds56008 := by
 decide +kernel
def cuts56009 : List PrefixCut := [⟨63,215018470,215018590⟩,
⟨64,218390678,218390800⟩]
theorem checked56009 : checkPrefixCuts (2^48) 7345143809 10 Manual.Count131072.C056009.packed 64 cuts56009 = true := by
 decide +kernel
def pointBounds56009 : List (Nat × Nat × Nat) := [(7345272832,113065948732205,113066336654830)]
theorem point_links_checked56009 : (cuts56009.take 1).map (fun c => (7345143809-1+2*2^10*c.k,113065733713735+c.lower,113066121636240+c.upper)) = pointBounds56009 := by
 decide +kernel
def cuts56010 : List PrefixCut := [⟨64,225207803,225207930⟩]
theorem checked56010 : checkPrefixCuts (2^48) 7345274881 10 Manual.Count131072.C056010.packed 64 cuts56010 = true := by
 decide +kernel
def cuts56011 : List PrefixCut := [⟨48,166345396,166345489⟩,
⟨64,220950337,220950462⟩]
theorem checked56011 : checkPrefixCuts (2^48) 7345405953 10 Manual.Count131072.C056011.packed 64 cuts56011 = true := by
 decide +kernel
def pointBounds56011 : List (Nat × Nat × Nat) := [(7345504256,113066343657612,113066731580459)]
theorem point_links_checked56011 : (cuts56011.take 1).map (fun c => (7345405953-1+2*2^10*c.k,113066177312216+c.lower,113066565234970+c.upper)) = pointBounds56011 := by
 decide +kernel
def cuts56012 : List PrefixCut := [⟨64,223820284,223820409⟩]
theorem checked56012 : checkPrefixCuts (2^48) 7345537025 10 Manual.Count131072.C056012.packed 64 cuts56012 = true := by
 decide +kernel
def cuts56013 : List PrefixCut := [⟨33,113153978,113154042⟩,
⟨64,218873249,218873374⟩]
theorem checked56013 : checkPrefixCuts (2^48) 7345668097 10 Manual.Count131072.C056013.packed 64 cuts56013 = true := by
 decide +kernel
def pointBounds56013 : List (Nat × Nat × Nat) := [(7345735680,113066735236815,113067123159883)]
theorem point_links_checked56013 : (cuts56013.take 1).map (fun c => (7345668097-1+2*2^10*c.k,113066622082837+c.lower,113067010005841+c.upper)) = pointBounds56013 := by
 decide +kernel
def cuts56014 : List PrefixCut := [⟨64,219750659,219750781⟩]
theorem checked56014 : checkPrefixCuts (2^48) 7345799169 10 Manual.Count131072.C056014.packed 64 cuts56014 = true := by
 decide +kernel
def cuts56015 : List PrefixCut := [⟨18,61268925,61268961⟩,
⟨64,219248614,219248741⟩]
theorem checked56015 : checkPrefixCuts (2^48) 7345930241 10 Manual.Count131072.C056015.packed 64 cuts56015 = true := by
 decide +kernel
def pointBounds56015 : List (Nat × Nat × Nat) := [(7345967104,113067121975670,113067509898957)]
theorem point_links_checked56015 : (cuts56015.take 1).map (fun c => (7345930241-1+2*2^10*c.k,113067060706745+c.lower,113067448629996+c.upper)) = pointBounds56015 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S6.B000187
