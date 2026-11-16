import PlattPointSubsetKernel
import PlattPointPackets.S8B000000
import PlattPointPackets.S8B000001
import PlattPointPackets.S8B000002
import PlattPointPackets.S8B000003
import PlattPointPackets.S8B000004
import PlattPointPackets.S8B000005
import PlattPointPackets.S8B000006
import PlattPointPackets.S8B000007
import PlattPointPackets.S8B000008
import PlattPointPackets.S8B000009
import PlattPointPackets.S8B000010
import PlattPointPackets.S8B000011
import PlattPointPackets.S8B000012
import PlattPointPackets.S8B000013
import PlattPointPackets.S8B000014
import PlattPointPackets.S8B000015
import PlattPointPackets.S8B000016
import PlattPointPackets.S8B000017
import PlattGlobalGrid.S8B000106
namespace ChenEffective.PlattWindow.PointCovers.S8B000106
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((((((((((((((((ChenEffective.PlattWindow.PointPackets.S8B000000.points ++ ChenEffective.PlattWindow.PointPackets.S8B000001.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000002.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000003.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000004.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000005.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000006.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000007.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000008.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000009.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000010.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000011.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000012.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000013.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000014.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000015.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000016.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000017.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S8B000106.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S8B000106.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S8B000106
