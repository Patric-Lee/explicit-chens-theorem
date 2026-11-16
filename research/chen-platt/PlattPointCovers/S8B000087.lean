import PlattPointSubsetKernel
import PlattPointPackets.S7B000003
import PlattPointPackets.S7B000004
import PlattPointPackets.S7B000005
import PlattPointPackets.S7B000006
import PlattPointPackets.S7B000007
import PlattPointPackets.S7B000008
import PlattPointPackets.S7B000009
import PlattPointPackets.S7B000010
import PlattPointPackets.S7B000011
import PlattPointPackets.S7B000012
import PlattPointPackets.S7B000013
import PlattPointPackets.S7B000014
import PlattPointPackets.S7B000015
import PlattPointPackets.S7B000016
import PlattPointPackets.S7B000017
import PlattPointPackets.S7B000018
import PlattGlobalGrid.S8B000087
namespace ChenEffective.PlattWindow.PointCovers.S8B000087
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((((((((((((((ChenEffective.PlattWindow.PointPackets.S7B000003.points ++ ChenEffective.PlattWindow.PointPackets.S7B000004.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000005.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000006.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000007.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000008.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000009.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000010.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000011.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000012.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000013.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000014.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000015.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000016.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000017.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000018.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S8B000087.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S8B000087.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S8B000087
