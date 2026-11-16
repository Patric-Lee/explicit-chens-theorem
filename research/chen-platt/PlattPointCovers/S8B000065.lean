import PlattPointSubsetKernel
import PlattPointPackets.S6B000011
import PlattPointPackets.S6B000012
import PlattPointPackets.S6B000013
import PlattPointPackets.S6B000014
import PlattPointPackets.S6B000015
import PlattPointPackets.S6B000016
import PlattPointPackets.S6B000017
import PlattPointPackets.S6B000018
import PlattPointPackets.S6B000019
import PlattPointPackets.S6B000020
import PlattPointPackets.S6B000021
import PlattPointPackets.S6B000022
import PlattPointPackets.S6B000023
import PlattGlobalGrid.S8B000065
namespace ChenEffective.PlattWindow.PointCovers.S8B000065
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((((((((((((ChenEffective.PlattWindow.PointPackets.S6B000011.points ++ ChenEffective.PlattWindow.PointPackets.S6B000012.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000013.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000014.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000015.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000016.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000017.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000018.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000019.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000020.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000021.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000022.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000023.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S8B000065.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S8B000065.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S8B000065
