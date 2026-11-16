import PlattAssemblyKernel
import PlattCertificates.Count131072.C051888
import PlattCertificates.Count131072.C051889
import PlattCertificates.Count131072.C051890
import PlattCertificates.Count131072.C051891
import PlattCertificates.Count131072.C051892
import PlattCertificates.Count131072.C051893
import PlattCertificates.Count131072.C051894
import PlattCertificates.Count131072.C051895
import PlattCertificates.Count131072.C051896
import PlattCertificates.Count131072.C051897
import PlattCertificates.Count131072.C051898
import PlattCertificates.Count131072.C051899
import PlattCertificates.Count131072.C051900
import PlattCertificates.Count131072.C051901
import PlattCertificates.Count131072.C051902
import PlattCertificates.Count131072.C051903
import PlattCertificates.Count131072.C051904
import PlattCertificates.Count131072.C051905
import PlattCertificates.Count131072.C051906
import PlattCertificates.Count131072.C051907
import PlattCertificates.Count131072.C051908
import PlattCertificates.Count131072.C051909
import PlattCertificates.Count131072.C051910
import PlattCertificates.Count131072.C051911
import PlattCertificates.Count131072.C051912
import PlattCertificates.Count131072.C051913
import PlattCertificates.Count131072.C051914
import PlattCertificates.Count131072.C051915
import PlattCertificates.Count131072.C051916
import PlattCertificates.Count131072.C051917
import PlattCertificates.Count131072.C051918
import PlattCertificates.Count131072.C051919
namespace ChenEffective.PlattWindow.Assembly.Prefix.S6.B000059
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts51888 : List PrefixCut := [⟨64,239654751,239654887⟩]
theorem checked51888 : checkPrefixCuts (2^48) 6804996097 10 Manual.Count131072.C051888.packed 64 cuts51888 = true := by
 decide +kernel
def cuts51889 : List PrefixCut := [⟨3,11498681,11498687⟩,
⟨64,240725573,240725711⟩]
theorem checked51889 : checkPrefixCuts (2^48) 6805127169 10 Manual.Count131072.C051889.packed 64 cuts51889 = true := by
 decide +kernel
def pointBounds51889 : List (Nat × Nat × Nat) := [(6805133312,112118009270110,112118396654409)]
theorem point_links_checked51889 : (cuts51889.take 1).map (fun c => (6805127169-1+2*2^10*c.k,112117997771429+c.lower,112118385155722+c.upper)) = pointBounds51889 := by
 decide +kernel
def cuts51890 : List PrefixCut := [⟨43,160770671,160770761⟩,
⟨64,239852364,239852496⟩]
theorem checked51890 : checkPrefixCuts (2^48) 6805258241 10 Manual.Count131072.C051890.packed 64 cuts51890 = true := by
 decide +kernel
def pointBounds51890 : List (Nat × Nat × Nat) := [(6805346304,112118399267673,112118786652194)]
theorem point_links_checked51890 : (cuts51890.take 1).map (fun c => (6805258241-1+2*2^10*c.k,112118238497002+c.lower,112118625881433+c.upper)) = pointBounds51890 := by
 decide +kernel
def cuts51891 : List PrefixCut := [⟨64,244025123,244025259⟩]
theorem checked51891 : checkPrefixCuts (2^48) 6805389313 10 Manual.Count131072.C051891.packed 64 cuts51891 = true := by
 decide +kernel
def cuts51892 : List PrefixCut := [⟨19,71014555,71014594⟩,
⟨64,238188738,238188872⟩]
theorem checked51892 : checkPrefixCuts (2^48) 6805520385 10 Manual.Count131072.C051892.packed 64 cuts51892 = true := by
 decide +kernel
def pointBounds51892 : List (Nat × Nat × Nat) := [(6805559296,112118793389044,112119180773782)]
theorem point_links_checked51892 : (cuts51892.take 1).map (fun c => (6805520385-1+2*2^10*c.k,112118722374489+c.lower,112119109759188+c.upper)) = pointBounds51892 := by
 decide +kernel
def cuts51893 : List PrefixCut := [⟨59,222964365,222964491⟩,
⟨64,241658285,241658421⟩]
theorem checked51893 : checkPrefixCuts (2^48) 6805651457 10 Manual.Count131072.C051893.packed 64 cuts51893 = true := by
 decide +kernel
def pointBounds51893 : List (Nat × Nat × Nat) := [(6805772288,112119183527592,112119570912551)]
theorem point_links_checked51893 : (cuts51893.take 1).map (fun c => (6805651457-1+2*2^10*c.k,112118960563227+c.lower,112119347948060+c.upper)) = pointBounds51893 := by
 decide +kernel
def cuts51894 : List PrefixCut := [⟨64,237890084,237890219⟩]
theorem checked51894 : checkPrefixCuts (2^48) 6805782529 10 Manual.Count131072.C051894.packed 64 cuts51894 = true := by
 decide +kernel
def cuts51895 : List PrefixCut := [⟨35,129737487,129737563⟩,
⟨64,237430553,237430691⟩]
theorem checked51895 : checkPrefixCuts (2^48) 6805913601 10 Manual.Count131072.C051895.packed 64 cuts51895 = true := by
 decide +kernel
def pointBounds51895 : List (Nat × Nat × Nat) := [(6805985280,112119569849083,112119957234263)]
theorem point_links_checked51895 : (cuts51895.take 1).map (fun c => (6805913601-1+2*2^10*c.k,112119440111596+c.lower,112119827496700+c.upper)) = pointBounds51895 := by
 decide +kernel
def cuts51896 : List PrefixCut := [⟨64,239286999,239287132⟩]
theorem checked51896 : checkPrefixCuts (2^48) 6806044673 10 Manual.Count131072.C051896.packed 64 cuts51896 = true := by
 decide +kernel
def cuts51897 : List PrefixCut := [⟨11,41769300,41769323⟩,
⟨64,241350187,241350320⟩]
theorem checked51897 : checkPrefixCuts (2^48) 6806175745 10 Manual.Count131072.C051897.packed 64 cuts51897 = true := by
 decide +kernel
def pointBounds51897 : List (Nat × Nat × Nat) := [(6806198272,112119958598448,112120345983846)]
theorem point_links_checked51897 : (cuts51897.take 1).map (fun c => (6806175745-1+2*2^10*c.k,112119916829148+c.lower,112120304214523+c.upper)) = pointBounds51897 := by
 decide +kernel
def cuts51898 : List PrefixCut := [⟨51,190686509,190686618⟩,
⟨64,238161238,238161374⟩]
theorem checked51898 : checkPrefixCuts (2^48) 6806306817 10 Manual.Count131072.C051898.packed 64 cuts51898 = true := by
 decide +kernel
def pointBounds51898 : List (Nat × Nat × Nat) := [(6806411264,112120348865844,112120736251461)]
theorem point_links_checked51898 : (cuts51898.take 1).map (fun c => (6806306817-1+2*2^10*c.k,112120158179335+c.lower,112120545564843+c.upper)) = pointBounds51898 := by
 decide +kernel
def cuts51899 : List PrefixCut := [⟨64,238363402,238363540⟩]
theorem checked51899 : checkPrefixCuts (2^48) 6806437889 10 Manual.Count131072.C051899.packed 64 cuts51899 = true := by
 decide +kernel
def cuts51900 : List PrefixCut := [⟨27,100612464,100612521⟩,
⟨64,240261044,240261179⟩]
theorem checked51900 : checkPrefixCuts (2^48) 6806568961 10 Manual.Count131072.C051900.packed 64 cuts51900 = true := by
 decide +kernel
def pointBounds51900 : List (Nat × Nat × Nat) := [(6806624256,112120735316439,112121122702278)]
theorem point_links_checked51900 : (cuts51900.take 1).map (fun c => (6806568961-1+2*2^10*c.k,112120634703975+c.lower,112121022089757+c.upper)) = pointBounds51900 := by
 decide +kernel
def cuts51901 : List PrefixCut := [⟨64,240918066,240918203⟩]
theorem checked51901 : checkPrefixCuts (2^48) 6806700033 10 Manual.Count131072.C051901.packed 64 cuts51901 = true := by
 decide +kernel
def cuts51902 : List PrefixCut := [⟨3,11164988,11164994⟩,
⟨64,241409621,241409753⟩]
theorem checked51902 : checkPrefixCuts (2^48) 6806831105 10 Manual.Count131072.C051902.packed 64 cuts51902 = true := by
 decide +kernel
def pointBounds51902 : List (Nat × Nat × Nat) := [(6806837248,112121127048073,112121514434133)]
theorem point_links_checked51902 : (cuts51902.take 1).map (fun c => (6806831105-1+2*2^10*c.k,112121115883085+c.lower,112121503269139+c.upper)) = pointBounds51902 := by
 decide +kernel
def cuts51903 : List PrefixCut := [⟨43,159944755,159944848⟩,
⟨64,237311287,237311425⟩]
theorem checked51903 : checkPrefixCuts (2^48) 6806962177 10 Manual.Count131072.C051903.packed 64 cuts51903 = true := by
 decide +kernel
def pointBounds51903 : List (Nat × Nat × Nat) := [(6807050240,112121517237461,112121904623740)]
theorem point_links_checked51903 : (cuts51903.take 1).map (fun c => (6806962177-1+2*2^10*c.k,112121357292706+c.lower,112121744678892+c.upper)) = pointBounds51903 := by
 decide +kernel
def cuts51904 : List PrefixCut := [⟨64,240449281,240449419⟩]
theorem checked51904 : checkPrefixCuts (2^48) 6807093249 10 Manual.Count131072.C051904.packed 64 cuts51904 = true := by
 decide +kernel
def cuts51905 : List PrefixCut := [⟨19,68970663,68970702⟩,
⟨64,235854903,235855035⟩]
theorem checked51905 : checkPrefixCuts (2^48) 6807224321 10 Manual.Count131072.C051905.packed 64 cuts51905 = true := by
 decide +kernel
def pointBounds51905 : List (Nat × Nat × Nat) := [(6807263232,112121904023937,112122291410438)]
theorem point_links_checked51905 : (cuts51905.take 1).map (fun c => (6807224321-1+2*2^10*c.k,112121835053274+c.lower,112122222439736+c.upper)) = pointBounds51905 := by
 decide +kernel
def cuts51906 : List PrefixCut := [⟨59,221295965,221296091⟩,
⟨64,241018902,241019039⟩]
theorem checked51906 : checkPrefixCuts (2^48) 6807355393 10 Manual.Count131072.C051906.packed 64 cuts51906 = true := by
 decide +kernel
def pointBounds51906 : List (Nat × Nat × Nat) := [(6807476224,112122292204142,112122679590862)]
theorem point_links_checked51906 : (cuts51906.take 1).map (fun c => (6807355393-1+2*2^10*c.k,112122070908177+c.lower,112122458294771+c.upper)) = pointBounds51906 := by
 decide +kernel
def cuts51907 : List PrefixCut := [⟨64,240559421,240559556⟩]
theorem checked51907 : checkPrefixCuts (2^48) 6807486465 10 Manual.Count131072.C051907.packed 64 cuts51907 = true := by
 decide +kernel
def cuts51908 : List PrefixCut := [⟨35,129705010,129705086⟩,
⟨64,238446129,238446268⟩]
theorem checked51908 : checkPrefixCuts (2^48) 6807617537 10 Manual.Count131072.C051908.packed 64 cuts51908 = true := by
 decide +kernel
def pointBounds51908 : List (Nat × Nat × Nat) := [(6807689216,112122682191510,112123069578452)]
theorem point_links_checked51908 : (cuts51908.take 1).map (fun c => (6807617537-1+2*2^10*c.k,112122552486500+c.lower,112122939873366+c.upper)) = pointBounds51908 := by
 decide +kernel
def cuts51909 : List PrefixCut := [⟨64,238855018,238855154⟩]
theorem checked51909 : checkPrefixCuts (2^48) 6807748609 10 Manual.Count131072.C051909.packed 64 cuts51909 = true := by
 decide +kernel
def cuts51910 : List PrefixCut := [⟨11,41841532,41841559⟩,
⟨64,237816798,237816936⟩]
theorem checked51910 : checkPrefixCuts (2^48) 6807879681 10 Manual.Count131072.C051910.packed 64 cuts51910 = true := by
 decide +kernel
def pointBounds51910 : List (Nat × Nat × Nat) := [(6807902208,112123071629179,112123459016347)]
theorem point_links_checked51910 : (cuts51910.take 1).map (fun c => (6807879681-1+2*2^10*c.k,112123029787647+c.lower,112123417174788+c.upper)) = pointBounds51910 := by
 decide +kernel
def cuts51911 : List PrefixCut := [⟨51,190142628,190142737⟩,
⟨64,240334181,240334318⟩]
theorem checked51911 : checkPrefixCuts (2^48) 6808010753 10 Manual.Count131072.C051911.packed 64 cuts51911 = true := by
 decide +kernel
def pointBounds51911 : List (Nat × Nat × Nat) := [(6808115200,112123457747073,112123845134461)]
theorem point_links_checked51911 : (cuts51911.take 1).map (fun c => (6808010753-1+2*2^10*c.k,112123267604445+c.lower,112123654991724+c.upper)) = pointBounds51911 := by
 decide +kernel
def cuts51912 : List PrefixCut := [⟨64,239585408,239585543⟩]
theorem checked51912 : checkPrefixCuts (2^48) 6808141825 10 Manual.Count131072.C051912.packed 64 cuts51912 = true := by
 decide +kernel
def cuts51913 : List PrefixCut := [⟨27,99801757,99801814⟩,
⟨64,235363819,235363952⟩]
theorem checked51913 : checkPrefixCuts (2^48) 6808272897 10 Manual.Count131072.C051913.packed 64 cuts51913 = true := by
 decide +kernel
def pointBounds51913 : List (Nat × Nat × Nat) := [(6808328192,112123847325791,112124234713399)]
theorem point_links_checked51913 : (cuts51913.take 1).map (fun c => (6808272897-1+2*2^10*c.k,112123747524034+c.lower,112124134911585+c.upper)) = pointBounds51913 := by
 decide +kernel
def cuts51914 : List PrefixCut := [⟨64,241023150,241023290⟩]
theorem checked51914 : checkPrefixCuts (2^48) 6808403969 10 Manual.Count131072.C051914.packed 64 cuts51914 = true := by
 decide +kernel
def cuts51915 : List PrefixCut := [⟨3,11616951,11616957⟩,
⟨64,239943640,239943772⟩]
theorem checked51915 : checkPrefixCuts (2^48) 6808535041 10 Manual.Count131072.C051915.packed 64 cuts51915 = true := by
 decide +kernel
def pointBounds51915 : List (Nat × Nat × Nat) := [(6808541184,112124235527954,112124622915784)]
theorem point_links_checked51915 : (cuts51915.take 1).map (fun c => (6808535041-1+2*2^10*c.k,112124223911003+c.lower,112124611298827+c.upper)) = pointBounds51915 := by
 decide +kernel
def cuts51916 : List PrefixCut := [⟨43,164038748,164038842⟩,
⟨64,240228391,240228529⟩]
theorem checked51916 : checkPrefixCuts (2^48) 6808666113 10 Manual.Count131072.C051916.packed 64 cuts51916 = true := by
 decide +kernel
def pointBounds51916 : List (Nat × Nat × Nat) := [(6808754176,112124627893391,112125015281441)]
theorem point_links_checked51916 : (cuts51916.take 1).map (fun c => (6808666113-1+2*2^10*c.k,112124463854643+c.lower,112124851242599+c.upper)) = pointBounds51916 := by
 decide +kernel
def cuts51917 : List PrefixCut := [⟨64,244564427,244564565⟩]
theorem checked51917 : checkPrefixCuts (2^48) 6808797185 10 Manual.Count131072.C051917.packed 64 cuts51917 = true := by
 decide +kernel
def cuts51918 : List PrefixCut := [⟨19,71805795,71805833⟩,
⟨64,236705360,236705491⟩]
theorem checked51918 : checkPrefixCuts (2^48) 6808928257 10 Manual.Count131072.C051918.packed 64 cuts51918 = true := by
 decide +kernel
def pointBounds51918 : List (Nat × Nat × Nat) := [(6808967168,112125020453256,112125407841526)]
theorem point_links_checked51918 : (cuts51918.take 1).map (fun c => (6808928257-1+2*2^10*c.k,112124948647461+c.lower,112125336035693+c.upper)) = pointBounds51918 := by
 decide +kernel
def cuts51919 : List PrefixCut := [⟨59,221860660,221860786⟩,
⟨64,240545222,240545360⟩]
theorem checked51919 : checkPrefixCuts (2^48) 6809059329 10 Manual.Count131072.C051919.packed 64 cuts51919 = true := by
 decide +kernel
def pointBounds51919 : List (Nat × Nat × Nat) := [(6809180160,112125407213481,112125794601970)]
theorem point_links_checked51919 : (cuts51919.take 1).map (fun c => (6809059329-1+2*2^10*c.k,112125185352821+c.lower,112125572741184+c.upper)) = pointBounds51919 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S6.B000059
