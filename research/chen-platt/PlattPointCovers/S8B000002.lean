import PlattPointSubsetKernel
import PlattPointPackets.S4B000009
import PlattPointPackets.S4B000010
import PlattPointPackets.S4B000011
import PlattPointPackets.S4B000012
import PlattPointPackets.S4B000013
import PlattPointPackets.S4B000014
import PlattPointPackets.S4B000015
import PlattPointPackets.S4B000016
import PlattPointPackets.S4B000017
import PlattGlobalGrid.S8B000002
namespace ChenEffective.PlattWindow.PointCovers.S8B000002
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((((((((ChenEffective.PlattWindow.PointPackets.S4B000009.points ++ ChenEffective.PlattWindow.PointPackets.S4B000010.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000011.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000012.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000013.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000014.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000015.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000016.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000017.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S8B000002.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S8B000002.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S8B000002
